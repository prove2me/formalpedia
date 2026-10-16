-- Prove2me | Theorems.Thm_SoftenDataShare_Mutual_zN_existsUnique
-- name    : SoftenDataShare.Mutual.zN_existsUnique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:12.960598+00:00
-- url     : https://prove2.me/theorems/80167e97-14b0-48e4-9874-ea9e81d78788
-- title:
--   Eq. (1) — the benchmark marginal consumer z^N = 1/2 + 1/h(z^N) exists and is unique
-- statement:
--   Let $(F,f)$ be a monotone-hazard-rate distribution on $[0,1]$ with hazard rate $h=f/(1-F)$. Then there is exactly one $z\in(1/2,1)$ with
--   $$z=\frac12+\frac1{h(z)}.$$
--
--   This number is the location $z^N$ of the marginal consumer in the benchmark without data sharing (Eq. (1)): firm 2's uniform price $p^N_2=2z^N-1$ makes consumer $z^N$ indifferent between the two firms. The paper defines $z^N$ through Eq. (1); this statement makes that definition well-posed, so every later result stated for "the $z^N$ satisfying (1)" is about a single, existing number.
--
--   **Formalization Note** The conclusion is `∃! z, IsZN F f z`, where `IsZN F f z` means $z\in(1/2,1)$ and $z=1/2+1/h(z)$.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), p. 8, Section 3.1, Eq. (1); uniqueness argument in the proof of Lemma 2, p. 34

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist
import Definitions.Def_SoftenDataShare_Mutual_Model

namespace SoftenDataShare.Mutual

theorem zN_existsUnique {F f : ℝ → ℝ} (hF : MHRDist F f) :
    ∃! z : ℝ, IsZN F f z := by sorry

end SoftenDataShare.Mutual
