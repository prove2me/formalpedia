-- Prove2me | Theorems.Thm_Plasticity_C0Sum_not_hasPlasticUnitBall_ell1_c0_nat
-- name    : Plasticity.C0Sum.not_hasPlasticUnitBall_ell1_c0_nat
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T20:09:44.208476+00:00
-- url     : https://prove2.me/theorems/1570ca83-5c94-4966-86d4-4c96eb71a36a
-- title:
--   The ball of $c_0(\mathbb N,\ell_1)\oplus_\infty c_0(\mathbb N,c_0)$ is not plastic
-- statement:
--   Let $Z=c_0(\mathbb N,\ell_1)\oplus_\infty c_0(\mathbb N,c_0)$, the $\ell_\infty$-product of the $c_0$-sum of countably many copies of $\ell_1=\ell_1(\mathbb N)$ and the $c_0$-sum of countably many copies of $c_0=c_0(\mathbb N)$.
--   The closed unit ball of $Z$ is not plastic.
-- source:
--   Proof draft 'Three constructions of nonplastic Banach unit balls' (ChatGPT Pro, OpenAI, 18 November 2026), Construction B and Lemma 2.2

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_SeqSpace
import Definitions.Def_Plasticity_C0Sum

namespace Plasticity
theorem C0Sum.not_hasPlasticUnitBall_ell1_c0_nat :
    ¬ HasPlasticUnitBall
      (c0Sum (fun _ : ℕ => lp (fun _ : ℕ => ℝ) 1) × c0Sum (fun _ : ℕ => c0 ℕ)) := by sorry
end Plasticity
