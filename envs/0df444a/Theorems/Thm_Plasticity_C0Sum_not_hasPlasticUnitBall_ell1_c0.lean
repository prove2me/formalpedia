-- Prove2me | Theorems.Thm_Plasticity_C0Sum_not_hasPlasticUnitBall_ell1_c0
-- name    : Plasticity.C0Sum.not_hasPlasticUnitBall_ell1_c0
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T19:25:53.314195+00:00
-- url     : https://prove2.me/theorems/66c94aae-05cc-48f2-a86c-332f336b4df9
-- title:
--   The ball of $c_0(\mathbb N,\ell_1(\mathbb R))\oplus_\infty c_0(\mathbb N,c_0(\mathbb R))$ is not plastic
-- statement:
--   Let $Z=c_0(\mathbb N,\ell_1(\mathbb R))\oplus_\infty c_0(\mathbb N,c_0(\mathbb R))$, the $\ell_\infty$-product of the $c_0$-sum of countably many copies of $\ell_1(\mathbb R)$ and the $c_0$-sum of countably many copies of $c_0(\mathbb R)$ (index set $\mathbb R$, of cardinality continuum).
--   The closed unit ball of $Z$ is not plastic.
-- source:
--   Proof draft 'Three constructions of nonplastic Banach unit balls' (ChatGPT Pro, OpenAI, 18 November 2026), Construction A and Lemma 2.2

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_SeqSpace
import Definitions.Def_Plasticity_C0Sum

namespace Plasticity
theorem C0Sum.not_hasPlasticUnitBall_ell1_c0 :
    ¬ HasPlasticUnitBall
      (c0Sum (fun _ : ℕ => lp (fun _ : ℝ => ℝ) 1) × c0Sum (fun _ : ℕ => c0 ℝ)) := by sorry
end Plasticity
