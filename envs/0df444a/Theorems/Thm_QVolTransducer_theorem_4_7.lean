-- Prove2me | Theorems.Thm_QVolTransducer_theorem_4_7
-- name    : QVolTransducer.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:33.721138+00:00
-- url     : https://prove2.me/theorems/9d98ed11-ccef-4d93-bb8e-d2e2fa3a7530
-- title:
--   Theorem 4.7 — amortized quantum-walk reflection through the stationary state $|\pi\rangle$
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $D$ be a set of inputs with oracles $O_x$ on a finite-dimensional space, and for every $x\in D$ let $P_x$ be an irreducible Markov chain on a fixed finite state space $\Omega$, reversible with respect to the distribution $\pi_x$ (its stationary distribution), with spectral gap $\gamma(P_x)$. For every $\omega\in\Omega$ let $C_\omega$ and $U_\omega$ be bidirectional canonical transducers on $\mathbb C^\Omega$ that construct the star state $|*_\omega\rangle=\sum_\nu\sqrt{P_x(\omega,\nu)}|\nu\rangle$ from a fixed reference state $|0\rangle$ and reflect through it. Then there is one bidirectional canonical transducer $U$ on $\mathbb C^\Omega$ such that for every input:
--
--   1. $|\pi\rangle\overset{U}{\rightsquigarrow}|\pi\rangle$ with complexity at most $c\sum_{\omega}\pi(\omega)\bigl(W(C_\omega,|0\rangle)+W(U_\omega,|*_\omega\rangle)\bigr)$;
--   2. $|\bar\pi\rangle\overset{U}{\rightsquigarrow}-|\bar\pi\rangle$ with complexity at most
--
--   $$
--   c\Bigl(\frac{M\,\||\bar\pi\rangle\|^2}{\gamma(P)}+\sum_{\omega\in\Omega}\frac{|\bar\pi(\omega)|^2}{\pi(\omega)}\bigl(W(C_\omega,|0\rangle)+W(U_\omega,|*_\omega\rangle)\bigr)\Bigr)
--   $$
--
--   for every net-flow $\bar\pi\in\mathbb C^\Omega$, where $|\pi\rangle=\sum_\omega\sqrt{\pi(\omega)}|\omega\rangle$, $|\bar\pi\rangle=\sum_\omega\frac{\bar\pi(\omega)}{\sqrt{\pi(\omega)}}|\omega\rangle$ and
--
--   $$
--   M:=\sup\bigl\{W(U_\omega,|\perp\rangle):\ \omega\in\Omega,\ |\perp\rangle\in\mathbb C^\Omega,\ \||\perp\rangle\|=1,\ \langle\perp|*_\omega\rangle=0\bigr\}. \tag{8}
--   $$
--
--   This is the framework's amortized quantum walk: the cost on $|\pi\rangle$ is an average of the local star-state costs, not a worst case divided by the spectral gap.
--
--   **Formalization Note** The chain is described by the published `MarkovMixing` predicates (stochastic, irreducible, detailed balance with a distribution) and `MarkovMixing.spectralGap` $=1-\lambda_2$, where $\lambda_2$ is the largest real eigenvalue different from $1$.
--
--   Differences from the source:
--   - reading: Hilbert spaces (oracle space, workspaces) → finite-dimensional coordinate spaces over finite index types; reason: the transduction complexity of Definition 2.7 is a minimum, which exists in finite dimension (Theorem 2.8); Ω is finite, and Part II uses only finite dimension (p.36)
--   - reading: the implicit input (P, the star states and the transducers depend on it; Ω does not) → an explicit input set D with oracles O_x, chains P_x and distributions π_x on a fixed Ω; C_ω, U_ω and U are single canonical transducers for all inputs; reason: Definition 2.10 and the convention stated before Lemma 4.5 and Theorem 4.7 (pp.31–32)
--   - encoding: γ(P) := 1 − λ with λ the second-largest eigenvalue (Definition 2.24) → MarkovMixing.spectralGap P = 1 − (largest real eigenvalue ≠ 1); reason: for an irreducible reversible chain the eigenvalues are real and 1 is simple, so the two coincide
--   - reading: |0⟩, "an arbitrary reference state" → the basis vector |ω₀⟩ of a fixed ω₀ ∈ Ω; reason: proof of Lemma 4.6, p.32
--   - encoding: irreducible, reversible Markov chain with stationary distribution π → IsStochastic, Irreducible, IsDist π and detailed balance; reason: Definitions 2.17 and 2.19; detailed balance implies stationarity
--   - encoding: O(·) complexity → ∃ universal c > 0 fixed before every parameter, K and ζ, with W ≤ c·(bound); reason: paper.md decision 4
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 4.7, pp.32–33 (PDF pp.34–35)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_mm_basic
import Definitions.Def_mm_spectral
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_starState

namespace QVolTransducer

open QAlgorithms

/-- **Amortized reflection through the stationary state** (Cornelissen, Apers, Gribling, *Improved
quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version
of November 3, 2026, sha256 40d7b52d…), Theorem 4.7, pp.32–33 (PDF pp.34–35)).

There is a universal constant `c > 0` with the following property. Let `D` be the (implicit) set of
inputs, with oracles `O_x ∈ U(H)`, and for every `x ∈ D` let `P_x` be an irreducible Markov chain
on the fixed finite state space `Ω`, reversible with respect to the distribution `π_x` (so `π_x`
is its stationary distribution), with spectral gap `γ(P_x)`. For every `ω ∈ Ω` let `C_ω` and `U_ω`
be bidirectional canonical transducers on the public space `ℂ^Ω` that construct the star state
`|∗_ω⟩ = Σ_ν √(P_x(ω,ν)) |ν⟩` from a fixed reference state `|0⟩` and reflect through it. Then there
is one bidirectional canonical transducer `U` on `ℂ^Ω` that reflects through `|π⟩ = Σ_ω √π(ω)|ω⟩`:
1. `|π⟩ ⇝_U |π⟩` with complexity at most `c Σ_ω π(ω)(W(C_ω,|0⟩) + W(U_ω,|∗_ω⟩))`;
2. `|π̄⟩ ⇝_U −|π̄⟩` with complexity at most
   `c (M ‖|π̄⟩‖²/γ(P) + Σ_ω |π̄(ω)|²/π(ω) (W(C_ω,|0⟩) + W(U_ω,|∗_ω⟩)))` for every net-flow
   `π̄ ∈ ℂ^Ω` (`Σ_ω π̄(ω) = 0`), where `|π̄⟩ = Σ_ω π̄(ω)/√π(ω) |ω⟩` and
   `M := sup{W(U_ω, |⊥⟩) : ω ∈ Ω, |⊥⟩ ∈ ℂ^Ω, ‖|⊥⟩‖ = 1, ⟨⊥|∗_ω⟩ = 0}` (8).

**Formalization Note** The chain may depend on the input but its state space may not (p.32). The
spectral gap is the published `MarkovMixing.spectralGap = 1 − λ₂`, with `λ₂` the largest real
eigenvalue different from `1` (the second-largest eigenvalue for an irreducible reversible chain,
Definition 2.24). The reference state `|0⟩` is the basis vector of a fixed `ω₀ ∈ Ω` ("an arbitrary
reference state", p.32). Spaces are finite-dimensional, and `O(·)` is a universal constant `c`. -/
theorem theorem_4_7 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω H : Type) [Fintype Ω] [DecidableEq Ω] [Fintype H] [DecidableEq H]
        (D : Type) (O : D → Matrix.unitaryGroup H ℂ) (P : D → Matrix Ω Ω ℝ) (π : D → Ω → ℝ)
        (ω₀ : Ω) (nC nU : Ω → ℕ) (C : ∀ ω, BiCanonical Ω H (Fin (nC ω)))
        (U : ∀ ω, BiCanonical Ω H (Fin (nU ω))),
        (∀ x, MarkovMixing.IsStochastic (P x)) → (∀ x, MarkovMixing.Irreducible (P x)) →
        (∀ x, MarkovMixing.IsDist (π x)) → (∀ x, MarkovMixing.DetailedBalance (P x) (π x)) →
        (∀ x ω, Transduces ((C ω).apply (O x)) (ket ω₀) (starState (P x) ω)) →
        (∀ x ω, Transduces ((U ω).apply (O x)) (starState (P x) ω) (starState (P x) ω)) →
        (∀ x ω (φ : EuclideanSpace ℂ Ω), inner ℂ (starState (P x) ω) φ = 0 →
          Transduces ((U ω).apply (O x)) φ (-φ)) →
        ∃ (n : ℕ) (Ut : BiCanonical Ω H (Fin n)), ∀ x,
          TransducesWithin (Ut.apply (O x)) (sqrtVec (π x)) (sqrtVec (π x))
            (c * ∑ ω, π x ω *
              (transductionComplexity ((C ω).apply (O x)) (ket ω₀) +
                transductionComplexity ((U ω).apply (O x)) (starState (P x) ω))) ∧
          ∀ πbar : Ω → ℂ, ∑ ω, πbar ω = 0 →
            TransducesWithin (Ut.apply (O x)) (flowVec (π x) πbar) (-flowVec (π x) πbar)
              (c * (sSup {m : ℝ | ∃ (ω : Ω) (φ : EuclideanSpace ℂ Ω), ‖φ‖ = 1 ∧
                      inner ℂ φ (starState (P x) ω) = 0 ∧
                      m = transductionComplexity ((U ω).apply (O x)) φ} *
                    ‖flowVec (π x) πbar‖ ^ 2 / MarkovMixing.spectralGap (P x) +
                  ∑ ω, ‖πbar ω‖ ^ 2 / π x ω *
                    (transductionComplexity ((C ω).apply (O x)) (ket ω₀) +
                      transductionComplexity ((U ω).apply (O x)) (starState (P x) ω)))) := by sorry

end QVolTransducer
