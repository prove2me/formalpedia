-- Prove2me | Theorems.Thm_WeierstrassCurve_isSemistableModel_of_modEq
-- name    : WeierstrassCurve.isSemistableModel_of_modEq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/1a8410f9-8cea-549f-9c73-bb59718abc28
-- title:
--   Semistability transfers to a congruent integral model
-- statement:
--   Let $W$ and $W'$ be Weierstrass curves over $\mathbb{Z}$, given by coefficients $a_1,a_2,a_3,a_4,a_6$, and let $n$ be an integer. Assume that $W$ satisfies the predicate [`WeierstrassCurve.IsSemistableModel`](def/FLTPrelim_Modularity.html#L85), that is: for every prime number $p$, if $p$ divides the discriminant $\Delta(W)$ then $p$ does not divide $c_4(W)$. Assume further that the five coefficients of $W'$ are congruent to those of $W$ modulo $n$, i.e. $a_i(W') \equiv a_i(W) \pmod{n}$ for $i = 1,2,3,4,6$, and that for every prime number $p$ with $p \nmid n$, if $p \mid c_4(W')$ then $p \nmid c_6(W')$. The conclusion is that $W'$ also satisfies [`WeierstrassCurve.IsSemistableModel`](def/FLTPrelim_Modularity.html#L85): for every prime $p$ dividing $\Delta(W')$, $p$ does not divide $c_4(W')$. Here $\Delta$, $c_4$ and $c_6$ denote the usual polynomial expressions in the $a_i$, so that the congruences modulo $n$ propagate to them, and $c_4^3 - c_6^2 = 1728\,\Delta$.
--
--   This is the assembly step for the local conditions on the auxiliary curve used in the $3$–$5$ switch: semistability of a model is deduced from closeness to a semistable model at the primes dividing $n$ together with coprimality of $c_4$ and $c_6$ away from them. It is used in the construction carried out by [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isSemistableModel_of_modEq.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Data.Int.ModEq
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.isSemistableModel_of_modEq {W W' : WeierstrassCurve ℤ} {n : ℤ} (hW : W.IsSemistableModel) (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₂ : W'.a₂ ≡ W.a₂ [ZMOD n]) (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n]) (h₄ : W'.a₄ ≡ W.a₄ [ZMOD n]) (h₆ : W'.a₆ ≡ W.a₆ [ZMOD n]) (haway : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ n → (p : ℤ) ∣ W'.c₄ → ¬ (p : ℤ) ∣ W'.c₆) : W'.IsSemistableModel := by sorry
