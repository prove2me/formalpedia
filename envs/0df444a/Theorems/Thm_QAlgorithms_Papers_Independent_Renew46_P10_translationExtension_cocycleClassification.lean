-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P10_translationExtension_cocycleClassification
-- name    : QAlgorithms.Papers.Independent.Renew46.P10.translationExtension_cocycleClassification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:04:58.404621+00:00
-- url     : https://prove2.me/theorems/d97e8903-437f-4bf7-bb5d-a59683c62199
-- title:
--   Extensions of subgroup translation actions and normalized twisted cocycles
-- statement:
--   Let $G$ be an abstract group, $H\trianglelefteq G$ a normal subgroup, and $L$ any set, possibly empty. Give $H\times L$ the right $H$-action $(h,\ell)\cdot r=(hr,\ell)$. Right $G$-actions extending this action correspond bijectively to pairs $(\star,c)$ consisting of a right $G$-action on $L$, trivial upon restriction to $H$, and a map $c:L\times G\to H$ such that, for every $\ell\in L$, $g,g'\in G$, and $h\in H$,
--
--   $$
--   c(\ell,gg')=c(\ell\star g,g')\,g'^{-1}c(\ell,g)g',\qquad c(\ell,h)=h.
--   $$
--
--   The bijection extracts $(c(\ell,g),\ell\star g)=(1,\ell)\cdot g$ and reconstructs
--
--   $$
--   (h,\ell)\cdot g=\bigl(c(\ell,hg),\ell\star g\bigr).
--   $$
--
--   Both constructions are inverse. Moreover,
--
--   $$
--   c(\ell,hg)=c(\ell,g)g^{-1}hg,
--   $$
--
--   and
--
--   $$
--   c(\ell\star g,g')g'^{-1}c(\ell,g)g'=c(\ell\star g,c(\ell,g)g').
--   $$
--
--   The original cocycle conditions are equivalently replaced by
--
--   $$
--   c(\ell,gg')=c(\ell\star g,c(\ell,g)g'),\qquad c(\ell,h)=h,
--   $$
--
--   with the same right action on $L$ trivial on $H$. All conjugation products are computed in $G$, using the inclusion of $H$.
--
--   This describes exactly the data needed to extend the translation action, including the canonical reconstruction. It is a statement about abstract groups and sets; no algebraic regularity or field hypothesis is involved.
--
--   **Formalization Note** The Lean statement uses explicit action-law predicates and two mutually inverse operations on the underlying functions. The source's dummy $r/h$ mismatch in reconstruction is corrected by consistently naming the first coordinate $h$.
-- source:
--   Reductive and unipotent actions of affine groups, arXiv:1406.4446v1, PDF p. 12, Observation 5.4, equations (4)–(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P10

namespace QAlgorithms.Papers.Independent.Renew46.P10

universe u v

/-- Observation 5.4, PDF p.12, equations (4)–(7): extension actions of an
abstract group G on H×L correspond to a right action on L trivial on the
normal subgroup H and a normalized twisted H-valued cocycle. Extraction at
(1,l) and the stated reconstruction are inverse; equations (5), (6), and the
alternative cocycle formulation (7) are included. The source's dummy h/r
mismatch in reconstruction is corrected by using its first coordinate.
No algebraic or characteristic assumptions apply to this observation. -/
theorem translationExtension_cocycleClassification
    {G : Type u} [Group G] (H : Subgroup G) [H.Normal] (L : Type v) :
    (∀ (act : (H × L) → G → (H × L)), TranslationExtension H act →
      TwistedCocycleData H (extensionBase act) (extensionCocycle act) ∧
      cocycleAction (extensionBase act) (extensionCocycle act) = act) ∧
    (∀ (star : L → G → L) (c : L → G → H), TwistedCocycleData H star c →
      TranslationExtension H (cocycleAction star c) ∧
      extensionBase (cocycleAction star c) = star ∧
      extensionCocycle (cocycleAction star c) = c ∧
      (∀ (l : L) (h : H) (g : G),
        (c l ((h : G) * g) : G) = (c l g : G) * g⁻¹ * (h : G) * g) ∧
      (∀ (l : L) (g g2 : G),
        (c (star l g) g2 : G) * g2⁻¹ * (c l g : G) * g2 =
          (c (star l g) ((c l g : G) * g2) : G))) ∧
    (∀ (star : L → G → L) (c : L → G → H),
      TwistedCocycleData H star c ↔ NestedCocycleData H star c) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P10
