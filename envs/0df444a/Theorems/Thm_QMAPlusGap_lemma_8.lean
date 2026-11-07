-- Prove2me | Theorems.Thm_QMAPlusGap_lemma_8
-- name    : QMAPlusGap.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:07:21.648614+00:00
-- url     : https://prove2.me/theorems/bc19c73a-1c2a-4a60-ab9c-191d9296e0a9
-- title:
--   Lemma 8 — threshold repetition: $1-e^{-\Omega(L)}$ and $s_0/\theta$ (corrected: $L\ge1$ in (ii))
-- statement:
--   Let $1>c_0>s_0>0$ and $s_0<\theta<c_0$. Let $0\preceq A\preceq I$ be an acceptance operator on a proof space $\mathcal W=\mathbb C^{\kappa}$, and for $L\in\mathbb N$ let $B$ be the threshold operator on $\mathcal H=\mathcal W^{\otimes L}$ that accepts iff at least $\lceil\theta L\rceil$ of the $L$ runs of $\{A,I-A\}$ accept.
--
--   1. There is $\kappa_0>0$, depending only on $c_0,s_0,\theta$, such that for every $\mathcal W$, $A$, every unit vector $|h\rangle\ge0$ with $\langle h|A|h\rangle\ge c_0$ and every $L$,
--   $$
--   \langle h^{\otimes L}|B|h^{\otimes L}\rangle\ \ge\ 1-e^{-\kappa_0L}.
--   $$
--   2. If $\langle h|A|h\rangle\le s_0$ for every unit $|h\rangle\ge0$ (a no instance), then for every $L\ge1$ and every unit $|\Psi\rangle\in\mathcal H$ with nonnegative amplitudes, possibly entangled across the $L$ registers,
--   $$
--   \langle\Psi|B|\Psi\rangle\ \le\ r:=\frac{s_0}{\theta}\ <\ 1 .
--   $$
--
--   The first part is the completeness of repetition; the second gives the constant $r<1$ that Proposition 9 needs, valid even for proofs entangled among the repetitions.
--
--   Differences from the source:
--   - correction: (ii) for an integer L → (ii) for L ≥ 1; reason: at L = 0, H is one-dimensional, B = I (the empty set has 0 ≥ ⌈0⌉ elements) and ⟨Ψ|B|Ψ⟩ = 1 > s0/θ
--   - generalization: c0, s0 the constants of Theorem 7; A the acceptance operator of the one-proof verifier on a fixed input; (i) for integers L → any constants 0 < s0 < θ < c0 < 1; every 0 ⪯ A ⪯ I on any finite ℂ^κ; (i) for every L ∈ ℕ including 0; reason: the proof uses only these inequalities and 0 ⪯ A ⪯ I; the constants of Theorem 7 and every acceptance operator are instances, and (i) holds trivially at L = 0
--   - reading: 1 − e^{−Ω(L)} → 1 − exp(−κ₀ L) with κ₀ > 0 depending only on (c0, s0, θ), chosen before κ, A, h and L; reason: the Ω-constant of a Chernoff bound depends only on the constants of the setting
--   - encoding: |h⟩ ≥ 0 (a proof state); 'the fixed input is a no instance' → h a unit vector with nonnegative amplitudes; the hypothesis ⟨h|A|h⟩ ≤ s0 for all unit h ≥ 0; reason: proof states are normalized; one-proof soundness is exactly this hypothesis
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 8, pp.14–15 (setting §3, p.14)

import Mathlib
import Definitions.Def_QMAPlusGap_IsNonnegVec
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_QMAPlusGap_expect
import Definitions.Def_QMAPlusGap_thresholdOp

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Lemma 8**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), pp.14–15. Setting (§3, p.14): one-proof constants `1 > c0 > s0 > 0` (Theorem 7), a
threshold `s0 < θ < c0`, a proof space `W = ℂ^κ` with acceptance operator `0 ⪯ A ⪯ I`, `H = W^{⊗L}`, and `B` the
threshold operator (accept iff at least `⌈θL⌉` of the `L` runs accept).

(i) "If |h⟩ ≥ 0 satisfies ⟨h|A|h⟩ ≥ c0, then ⟨h^{⊗L}|B|h^{⊗L}⟩ ≥ 1 − e^{−Ω(L)}." (ii) "If the fixed input is a no
instance, every normalized pure state |Ψ⟩ ∈ H with nonnegative amplitudes, including a state that may be entangled
among the L W-registers, satisfies ⟨Ψ|B|Ψ⟩ ≤ r := s0/θ < 1."

**Formalization Note** `e^{−Ω(L)}` is `exp(−κ₀ L)` for a `κ₀ > 0` depending only on `(c0, s0, θ)`, chosen before
`κ`, `A`, `h` and `L`. `h` is a unit vector (a proof state). "No instance" is the one-proof soundness
hypothesis `⟨h|A|h⟩ ≤ s0` for every unit `h ≥ 0`. (ii) is stated for `L ≥ 1` (corrected: at `L = 0`, `B = I` and
`⟨Ψ|B|Ψ⟩ = 1 > s0/θ`); (i) holds for every `L`. Real parts of the (real) expectations are compared. -/
theorem lemma_8 (c0 s0 θ : ℝ) (hs0 : 0 < s0) (hs0θ : s0 < θ) (hθc0 : θ < c0) (hc0 : c0 < 1) :
    (∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ), A.PosSemidef → (1 - A).PosSemidef →
        ∀ h : κ → ℂ, IsNonnegVec h → ArgmaxDeFinetti.vnorm h = 1 → c0 ≤ (expect A h).re →
        ∀ L : ℕ, 1 - Real.exp (-(κ₀ * L)) ≤
          (expect (thresholdOp A L θ) (fun z : Fin L → κ => ∏ i, h (z i))).re) ∧
    (∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ), A.PosSemidef → (1 - A).PosSemidef →
        (∀ h : κ → ℂ, IsNonnegVec h → ArgmaxDeFinetti.vnorm h = 1 → (expect A h).re ≤ s0) →
        ∀ L : ℕ, 1 ≤ L → ∀ Ψ : (Fin L → κ) → ℂ, IsNonnegVec Ψ → ArgmaxDeFinetti.vnorm Ψ = 1 →
          (expect (thresholdOp A L θ) Ψ).re ≤ s0 / θ) ∧
    s0 / θ < 1 := by sorry

end QMAPlusGap
