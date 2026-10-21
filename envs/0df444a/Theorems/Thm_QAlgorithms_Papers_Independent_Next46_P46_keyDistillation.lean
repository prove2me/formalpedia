-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P46_keyDistillation
-- name    : QAlgorithms.Papers.Independent.Next46.P46.keyDistillation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:01:31.168686+00:00
-- url     : https://prove2.me/theorems/e9f1f85a-f968-4049-b2e7-46ee14b62857
-- title:
--   One-way key distillation with forward cost H(X|B)
-- statement:
--   Let $P$ be a probability law on a finite nonempty alphabet and $(|\phi_x\rangle^{BE})_x$ an orthonormal family. Alice and Bob receive $n$ copies of the $AB$ marginal of $|\psi\rangle^{ABE}=\sum_x\sqrt{P(x)}|x\rangle^A|\phi_x\rangle^{BE}$, with Eve holding $E^n$. In the dephased source, put $C=H(X)-I(X;B)=H(X|B)$; in the coherent source, put $R=H(B)-H(AB)$.
--
--   For every $\varepsilon,\delta>0$, all sufficiently large positive $n$ admit a complete local Alice measurement with classical key $K_A$ and a public message $L$, followed by an $L$-dependent Bob POVM producing $K_B$, such that
--
--   $$
--   \frac{\log_2 M}{n}\ge R-\delta,\qquad
--   \frac{\log_2|\mathcal L|}{n}\le C+\delta,\qquad
--   \|\omega^{K_AK_BLE^n}-\Phi_M^{K_AK_B}\otimes\theta^{LE^n}\|_1\le\varepsilon.
--   $$
--
--   Here $\Phi_M=M^{-1}\sum_m|mm\rangle\!\langle mm|$ is a uniform classical key and $\theta$ is a normalized state. Eve receives the full public message. Completeness includes type selection, concentration and failure handling; finite branch probabilities are not assumed uniform.
--
--   This gives both the key yield and the forward communication budget.
-- source:
--   Relating quantum privacy and quantum coherence: an operational approach, arXiv:quant-ph/0307053v1, PDF p. 3, Key distillation (1.); communication count corrected using p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

/-- arXiv:quant-ph/0307053v1, PDF pp.1--3, scenario 1: key rate I_c and forward cost H(X|B).
SOURCE CORRECTION: p.3 prints nI(X|B)^+; its L formula and p.4 give nH(X|B)^+.
Complete POVMs include concentration/type overhead; no finite uniformity is assumed. -/
theorem keyDistillation {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    [Nonempty X] [Nonempty B] [Nonempty E]
    (p : X → ℝ) (hp : IsLaw p) (phi : X → Vec (B × E))
    (hphi : Orthonormal ℂ phi) :
    let psi := WithLp.toLp 2 (fun z : X × (B × E) => (Real.sqrt (p z.1) : ℂ) * phi z.1 z.2)
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
      ∀ n ≥ n0, ∃ C : StaticKeyProtocol X B n,
        C.Good (pureDensity psi) eps ∧
        coherentInfo (marginalAB (pureDensity psi)) - delta ≤
          Real.logb 2 (C.m : ℝ) / n ∧
        Real.logb 2 (C.l : ℝ) / n ≤ (classicalCosts p phi).1 + delta := by sorry

end QAlgorithms.Papers.Independent.Next46.P46

end
