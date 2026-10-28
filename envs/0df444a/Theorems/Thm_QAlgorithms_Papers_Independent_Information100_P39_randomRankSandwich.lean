-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_randomRankSandwich
-- name    : QAlgorithms.Papers.Independent.Information100.P39.randomRankSandwich
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:17:03.65498+00:00
-- url     : https://prove2.me/theorems/88a34304-cc68-4ff6-a09d-c4471ea9a19c
-- title:
--   Unnumbered random-rank sandwich, Eq.(7)
-- statement:
--   For independent Bernoulli faults with probabilities $p_a\in[0,1]$ and nested kernels $K_T\subseteq K_C\subseteq\mathbb F_2^M$, let $T$ and $C$ be the corresponding quotient maps. Choose a subset $\Gamma$ by independently retaining coordinate $a$ with probability $\theta_a=4p_a(1-p_a)$. Restrict the maps to vectors supported on $\Gamma$ and put $\kappa(\Gamma)=\dim T_\Gamma(\ker C_\Gamma)$. Then
--
--   $$\kappa(\Gamma)=\operatorname{rank}T_\Gamma-\operatorname{rank}C_\Gamma,\qquad
--   \Delta_1\ge (\log2)\,\mathbb E_\mu\kappa(\Gamma)\ge\Delta_2.$$
--
--   Here $\Delta_r=H_r(T(b))-H_r(C(b))$ and $\mu$ is the specified product subset law. The quantitative intermediate term also covers deterministic fault probabilities.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 2, Unnumbered random-rank sandwich, Eq.(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF pp.2–3, Eqs.(6)–(7): the random-rank sandwich and the rank formula. -/
theorem randomRankSandwich {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (KT KC : Submodule F2 (Bits m)) (hK : KT ≤ KC) :
    (∀ g, kappa KT KC g =
      Module.finrank F2 ((supported g).map KT.mkQ) -
      Module.finrank F2 ((supported g).map KC.mkQ)) ∧
    Real.log 2 * (∑ g : Finset (Fin m), erasedLaw p g * (kappa KT KC g : ℝ)) ≤
      linearDeficit p KT KC 1 ∧
    linearDeficit p KT KC 2 ≤
      Real.log 2 * (∑ g : Finset (Fin m), erasedLaw p g * (kappa KT KC g : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
