-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_packing
-- name    : QAlgorithms.Papers.Independent.Next46.P40.packing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:50:46.813011+00:00
-- url     : https://prove2.me/theorems/29107bb6-135e-422a-bb03-69d21f362c8a
-- title:
--   Packing with a nonempty codebook
-- statement:
--   Let $A$ be a finite nonzero register and let $S$ be a finite nonempty set. Let $\lambda_s\ge0$, $\sum_s\lambda_s=1$, and let $\sigma_s$ be density operators with average $\sigma=\sum_s\lambda_s\sigma_s$. Suppose orthogonal projectors $\Pi,\Pi_s$, positive integers $D,d$, and $\epsilon\ge0$ satisfy, for every $s$,
--
--   $$\operatorname{Tr}(\sigma_s\Pi_s)\ge1-\epsilon,\quad\operatorname{Tr}(\sigma_s\Pi)\ge1-\epsilon,\quad\operatorname{Tr}\Pi_s\le d,\quad\Pi\sigma\Pi\preceq D^{-1}\Pi.$$
--
--   For $0<\gamma<1$, put $N=\lfloor\gamma D/d\rfloor$ and assume $N\ge1$. There exist a map $f:\{0,\ldots,N-1\}\to S$ and one complete POVM $\{\Lambda_k\}_{k=0}^{N-1}$ such that
--
--   $$\operatorname{Tr}(\sigma_{f(k)}\Lambda_k)\ge1-4(\epsilon+\sqrt{8\epsilon})-8\gamma\qquad\text{for every }k.$$
--
--   The map need not be injective. The lemma supplies a codebook with a maximum-error guarantee. **Source correction:** the printed statement allows $N=0$; the added nonempty-codebook condition excludes the impossible complete empty POVM.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 4, Lemma 2, (19)–(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P40

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation marginalRB associate)

variable {A B C E R S : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R] [Fintype S]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

variable [DecidableEq R] [DecidableEq S]

/-- PDF p.4, Lemma 2, with the operational-domain correction N >= 1.
Printed: N = floor(gamma D/d), with no exclusion of N=0.
Changed: exclude N=0, because a complete zero-outcome POVM on a nonzero
register cannot exist. No injectivity of the sampled codebook is imposed. -/
theorem packing
    [Nonempty A] [Nonempty S]
    (weight : S → ℝ) (hw : ∀ s, 0 ≤ weight s) (hwsum : ∑ s, weight s = 1)
    (rho : S → Matrix A A ℂ) (hrho : ∀ s, IsDensityMatrix (rho s))
    (P : Matrix A A ℂ) (hP : IsProjector P)
    (Pm : S → Matrix A A ℂ) (hPm : ∀ s, IsProjector (Pm s))
    (D d : ℕ) (hD : 0 < D) (hd : 0 < d)
    (eps gamma : ℝ) (heps : 0 ≤ eps) (hg : 0 < gamma) (hg1 : gamma < 1)
    (hlocal : ∀ s, 1 - eps ≤ effectProb (Pm s) (rho s))
    (hglobal : ∀ s, 1 - eps ≤ effectProb P (rho s))
    (hdim : ∀ s, (Pm s).trace.re ≤ (d : ℝ))
    (hbound : (((D : ℂ)⁻¹ • P) -
      P * (∑ s, (weight s : ℂ) • rho s) * P).PosSemidef)
    (hN : 0 < ⌊gamma * (D : ℝ) / (d : ℝ)⌋₊) :
    ∃ (f : Fin ⌊gamma * (D : ℝ) / (d : ℝ)⌋₊ → S)
      (L : Fin ⌊gamma * (D : ℝ) / (d : ℝ)⌋₊ → Matrix A A ℂ),
      IsPOVM L ∧ ∀ k,
        1 - 4 * (eps + Real.sqrt (8 * eps)) - 8 * gamma ≤ effectProb (L k) (rho (f k)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end
