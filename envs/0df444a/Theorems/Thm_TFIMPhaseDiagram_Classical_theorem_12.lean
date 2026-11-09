-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_theorem_12
-- name    : TFIMPhaseDiagram.Classical.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:05:06.525568+00:00
-- url     : https://prove2.me/theorems/8478d7ae-70ac-4a31-a7ad-dcdf52328663
-- title:
--   Theorem 12 — KL contraction, TV mixing, and partition estimator; both parts
-- statement:
--   Fix $n\ge1$, $M\ge3$, well-defined cycle laws $\pi_i$, arbitrary signed couplings bounded by $K_M(\eta)$, and $\eta\ge0$, with the infinite bound at zero. Let $J$ be symmetric, $W(s)=\frac1{2M}\sum_{i,j}J_{ij}\langle s_i,s_j\rangle$, $\pi=\bigotimes_i\pi_i$, $\mu_\lambda=T_{\lambda W}\pi$, and $L=n\lceil\|J\|_\infty\rceil+1$.
--
--   1. For $0\le\lambda\le1$ with $\lambda\Delta(J)\alpha_M(\eta)<1$, put $C=(1-\lambda\Delta(J)\alpha_M(\eta))^{-1}$. From every initial probability law absolutely continuous with respect to $\mu_\lambda$, block Glauber dynamics satisfies
--   $$D_{\rm KL}(\rho^{(t+1)}\|\mu_\lambda)\le(1-1/(Cn))D_{\rm KL}(\rho^{(t)}\|\mu_\lambda).$$
--   From $\pi$, $t\ge2Cn\log(L/\epsilon_{\rm TV})$ gives TV error at most $\epsilon_{\rm TV}$. Sampling $\pi$ and each block step take $O(nM)$ time; thus approximate sampling takes $O(Cn^2M\log(L/\epsilon_{\rm TV}))$ time.
--
--   2. If $(1-1/L)\Delta(J)\alpha_M(\eta)<1$, partition estimation satisfies
--   $$\Pr[\widehat Z=\exp(\pm\epsilon)\mathbb E_\pi e^W]\ge1-\delta,$$
--   with time $O(C_*n^2M\log(L/\epsilon)L^2\epsilon^{-2}\log(1/\delta))$, where $C_*=(1-(1-1/L)\Delta(J)\alpha_M(\eta))^{-1}$. Integer budgets and all programs are uniform. Both zero-field parity limits and all compatible pins are included.
--
--   This theorem supplies the full mixing and counting interface for the quantum estimators.
--
--   Differences from the source:
--   - encoding: O(nM) routines and O(n squared M C log(L/epsilon) L squared epsilon^-2 log(1/delta)) estimator time → uniform finite programs with explicit mixingBudget and countingBudget integer witnesses; reason: Ceilings and additive 1 account for at least one instruction; the witnesses have the displayed source orders, with exact C=1/(1-lambda Delta alphaM).
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.8 = PDF p.8, Theorem 12

import Definitions.Def_TFIMPhaseDiagram_Classical_sampling

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Theorem 12, p.8, both parts and all sampling/cost clauses. Programs and constants are uniform. -/
theorem theorem_12 :
  ∃ (Pbase Pstep Pmix Pcount : RAMProgram) (a : ℕ),
    Admissible Pbase ∧ Admissible Pstep ∧ Admissible Pmix ∧ Admissible Pcount ∧ 0 < a ∧
    ∀ (n M : ℕ), 0 < n → 3 ≤ M →
    ∀ (K : Fin n → CycleParameters M) (w : Fin n → Fin M → Field),
    (∀ i, ValidCycle (K i) (w i)) →
    ∀ (J : Matrix (Fin n) (Fin n) ℝ), J.IsSymm →
    ∀ η : ℝ, 0 ≤ η → (∀ i, BoundedCycle η (K i)) →
    let π := systemBase K w
    let L := annealingLength J
    let input := systemInput K w J
    (SamplesSystem Pbase (a*n*M) n M input π 0) ∧
    (∀ (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
      let μ := systemTilt K w J lam
      (∀ x : Fin n → Spins M, (∀ i, 0 < specProb (K i) (w i) (x i)) →
        SamplesSystem Pstep (a*n*M) n M
          (input ++ [lam] ++ (List.finRange n).flatMap (fun i =>
            (List.finRange M).map (fun k => spin (x i k))))
          (systemRun K w J lam (Measure.dirac x) 1) 0) ∧
      (lam*spectralWidth J*alphaMesh M η < 1 →
        let C := 1/(1-lam*spectralWidth J*alphaMesh M η)
        (∀ (ρ : Measure (Fin n → Spins M)), IsProbabilityMeasure ρ → ρ ≪ μ →
          ∀ t : ℕ, klDiv (systemRun K w J lam ρ (t+1)) μ ≤
            ENNReal.ofReal (1-1/(C*n)) * klDiv (systemRun K w J lam ρ t) μ) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 →
          (∀ t : ℕ, (t : ℝ) ≥ 2*C*n*Real.log ((L : ℝ)/ε) →
            tv (systemRun K w J lam π t) μ ≤ ε) ∧
          SamplesSystem Pmix (mixingBudget a n M C L ε) n M (input ++ [lam,ε]) μ ε))) ∧
    ((1-1/(L : ℝ))*spectralWidth J*alphaMesh M η < 1 →
      let C := 1/(1-(1-1/(L : ℝ))*spectralWidth J*alphaMesh M η)
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      let b := countingBudget a n M L C ε δ
      let xs := input ++ [ε,δ]
      let out := ramOutput Pcount xs b
      HaltsWithin Pcount xs b ∧ Measurable out ∧
        1-δ ≤ MatMulTimeLP.tapeLaw.real {ω | ExpApprox ε (out ω)
          (∫ s, Real.exp (cycleInteraction J s) ∂π : ℝ)}) := by sorry
end TFIMPhaseDiagram.Classical
