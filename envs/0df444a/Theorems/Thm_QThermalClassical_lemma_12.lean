-- Prove2me | Theorems.Thm_QThermalClassical_lemma_12
-- name    : QThermalClassical.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:26.549527+00:00
-- url     : https://prove2.me/theorems/0cf36179-d778-4ba9-8253-a0eb2f5a6bae
-- title:
--   Lemma 12 — Gibbs state validity of one pinning iteration
-- statement:
--   Consider one iteration of Algorithm 1 for a Pauli Hamiltonian $H$, with $0<q<1$, unpinned sites $S$, a valid configuration $\chi$ satisfying the invariant of Lemma 11, and an admissible $a^*$. Let $(b_1,E_1)$ and $(b_2,E_2)$ be drawn independently from samplers with
--   $$
--   \mathbb E[I+b_iE_i]=e^{-\frac\beta2H(S)}e^{\frac\beta2\left(H(S)-H^{(S)}_{(a^*)}\right)}\qquad(i=1,2),
--   $$
--   and $J$ with probabilities $p_1=q$, $p_{J}=(1-q)/6$ ($J\neq1$). Then the new site set $\hat S$ and configuration $\hat\chi$ satisfy
--   $$
--   \mathbb E\left[e^{-\frac\beta2H(\hat S)}\sigma(\hat\chi)e^{-\frac\beta2H(\hat S)}\right]=e^{-\frac\beta2H(S)}\sigma(\chi)e^{-\frac\beta2H(S)}\qquad(87).
--   $$
--
--   Iterating (87) from $S=\Lambda$, $\chi=\emptyset$ gives $e^{-\beta H}=\mathbb E[\sigma(\chi)]$ at the end of the algorithm.
--
--   Differences from the source:
--   - reading: the expectation $\mathbb E$ over one iteration → independent samplers with block-wise expectations and $J$ drawn with $p_J$, summed over pairs of blocks; reason: lines 8–10 of Algorithm 1; the graded expectation of Lemma 9
--   - reading: the lemma is stated for the algorithm's iteration → hypotheses: $\chi$ valid with the invariant of Lemma 11, $a^*$ admissible, $0<q<1$; reason: this is the algorithm's state at every iteration; the proof uses that earlier monomials avoid $S$ (Lemma 11), and the divisions $1/p_J$ need every $p_J>0$
--   - generalization: inverse temperature $\beta$ → every real $\beta$; reason: (87) is an algebraic identity; it specializes to $\beta\ge0$
--   - generalization: $(b_i,E_i)$ outcomes of the sampling primitive (Pauli products up to a phase of terms in $A(S)$) → arbitrary outcomes $(b,E,C)$, only the expectation of $I+bE$ is assumed; reason: (91)–(93) use only the two expectations and that the earlier monomials avoid $S$; it specializes to the primitive's outcomes
--   - encoding: a Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ with distinct non-identity Pauli strings → a coefficient function $c$ on Pauli words with $c(I)=0$, $A=\{P: c_P\neq 0\}$; reason: distinctness is automatic and words with coefficient $0$ change neither $H$ nor any condition; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 12, eq. (87), p.29; Algorithm 1, p.27

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_restrictTouching
import Definitions.Def_QThermalClassical_propagator
import Definitions.Def_QThermalClassical_HasStepExpect

set_option autoImplicit false

namespace QThermalClassical

/-- **Lemma 12 (Gibbs state validity).** One iteration of Algorithm 1 produces `Ŝ` and `χ̂` with
`𝔼[e^{−(β/2)H(Ŝ)} σ(χ̂) e^{−(β/2)H(Ŝ)}] = e^{−(β/2)H(S)} σ(χ) e^{−(β/2)H(S)}` (87), the
expectation taken over the two independent samples `(b₁, E₁)`, `(b₂, E₂)` from samplers with
`𝔼[I + bE] = e^{−(β/2)H(S)} e^{(β/2)(H(S) − H^{(S)}_{(a*)})}` (lines 8–9) and over the branch
`J` (line 10).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 12, eq. (87), p.29; Algorithm 1, p.27.

**Formalization Note.** The configuration entering the iteration is valid and satisfies the
invariant of Lemma 11 (the situation of Algorithm 1 at the start of every iteration), `a*` is
an admissible choice, and `0 < q < 1` so that every branch probability `p_J` is positive, as
required by the divisions `1/p_J` in lines 12–24. `H` has no identity term (eq. (5)). The
identity holds for every real `β`. -/
theorem lemma_12 {Q : Type} [Fintype Q] [DecidableEq Q] (c : PauliWord Q → ℝ)
    (hc0 : c (fun _ => 0) = 0) (β q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (S : Finset Q) (χ : Config Q) (hχ : IsValidConfig χ) (hinv : PinInvariant S χ)
    (a : PauliWord Q) (ha : IsAdmissible c S χ a) (σ₁ σ₂ : Sampler Q)
    (h₁ : σ₁.HasExpect (fun o => 1 + ((o.b : ℝ) : ℂ) • o.E)
      (propagator (ham (restrictIn c S)) (ham (restrictTouching c S (pauliSupport a))) (β / 2)))
    (h₂ : σ₂.HasExpect (fun o => 1 + ((o.b : ℝ) : ℂ) • o.E)
      (propagator (ham (restrictIn c S)) (ham (restrictTouching c S (pauliSupport a))) (β / 2))) :
    HasStepExpect q σ₁ σ₂
      (fun o₁ o₂ J =>
        boltz (ham (restrictIn c (pinStep q S χ a o₁ o₂ J).1)) (β / 2) *
          sigma (pinStep q S χ a o₁ o₂ J).2 *
          boltz (ham (restrictIn c (pinStep q S χ a o₁ o₂ J).1)) (β / 2))
      (boltz (ham (restrictIn c S)) (β / 2) * sigma χ * boltz (ham (restrictIn c S)) (β / 2)) := by sorry

end QThermalClassical
