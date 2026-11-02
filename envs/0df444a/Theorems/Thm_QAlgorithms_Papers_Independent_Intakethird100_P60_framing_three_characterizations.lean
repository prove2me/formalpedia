-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P60_framing_three_characterizations
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P60.framing_three_characterizations
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:27:51.188632+00:00
-- url     : https://prove2.me/theorems/743847ca-0a27-4776-b97e-b3322e57a525
-- title:
--   Framing: three equivalent characterizations
-- statement:
--   Let $\mathbb D$ be a pseudo double category, with strict vertical category $\mathbb D_0$, weak horizontal composition $\odot$, and specified coherent globular associators and unitors. Let $L,R$ send a horizontal arrow or square to its left and right frame. Then
--
--   $$
--   (L,R)\text{ is a fibration}\quad\Longleftrightarrow\quad
--   (L,R)\text{ is an opfibration}\quad\Longleftrightarrow\quad
--   \text{every vertical arrow has both a companion and a conjoint}.
--   $$
--
--   For a vertical arrow $f:A\to B$, a companion is $M:A\rightsquigarrow B$ with cells $u:U_A\Rightarrow M$ over $(1_A,f)$ and $c:M\Rightarrow U_B$ over $(f,1_B)$. A conjoint is $N:B\rightsquigarrow A$ with cells $v:U_A\Rightarrow N$ over $(f,1_A)$ and $d:N\Rightarrow U_B$ over $(1_B,f)$. Their vertical composites equal $U_f$. Their horizontal composites, conjugated by the indicated unitors, are the identity cells of $M$ and $N$. The lifting properties quantify over every pair of further frame arrows and require unique factorization.
--
--   This characterizes nonalgebraic framing by typed companion and conjoint data, including all equations (4.3)–(4.4).
-- source:
--   Framed bicategories and monoidal fibrations, arXiv:0706.1286v2, PDF p. 15, Theorem 4.1: Three equivalent characterizations of framing

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P60

namespace QAlgorithms.Papers.Independent.Intakethird100.P60

open CategoryTheory

universe u v w x

/-- Theorem 4.1 (PDF p. 15): all three conditions, with both vertical and
horizontal identities included in the companion and conjoint data. -/
theorem framing_three_characterizations {V : Type u} [Category.{v} V]
    (D : DoubleData.{u,v,w,x} V) (hD : DoubleCoherence D) :
    (IsFrameFibration D ↔ IsFrameOpfibration D) ∧
    (IsFrameFibration D ↔ HasCompanions D ∧ HasConjoints D) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P60
