-- Prove2me | Theorems.Thm_ValuationSubring_exists_le_and_le_toLocalSubring_of_toSubring_le
-- name    : ValuationSubring.exists_le_and_le_toLocalSubring_of_toSubring_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/425b34e6-5608-5e54-af95-8964e6222ddd
-- title:
--   Valuation subring of O dominating a local subring of O
-- statement:
--   Let $K$ be a field, let $O$ be a valuation subring of $K$, and let $R$ be a local subring of $K$, i.e. a subring of $K$ whose underlying ring is local. Assume that $R$ is contained in $O$ as a subring of $K$. Then there exists a valuation subring $V$ of $K$ such that $V \le O$, i.e. $V$ is contained in $O$, and such that $R \le V$ as local subrings, the latter meaning that $R$ is contained in $V$ and that the resulting inclusion $R \hookrightarrow V$ is a local ring homomorphism: a element of $R$ that becomes a unit in $V$ is already a unit in $R$, equivalently $\mathfrak m_V \cap R = \mathfrak m_R$. Thus $V$ is a valuation subring of $K$ sandwiched between $R$ and $O$ which dominates $R$; note that the order relation on local subrings used in the conclusion is domination, not mere inclusion, whereas the hypothesis on $R$ and $O$ is plain inclusion of subrings.
--
--   This is the existence of a composite valuation dominating a prescribed local subring inside a given valuation ring: geometrically, if the local ring of a point $\eta$ of an integral scheme is a valuation ring and $\eta$ specialises to $x$, the statement produces a valuation of the function field centred at $x$ and refining $\eta$. It is used in the construction of Igusa-type charts on modular curves, in the statements about Drinfeld charts whose local rings are formally smooth localisations of a normal model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_le_and_le_toLocalSubring_of_toSubring_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem ValuationSubring.exists_le_and_le_toLocalSubring_of_toSubring_le
    {K : Type u} [Field K] (O : ValuationSubring K) (R : LocalSubring K)
    (hRO : R.toSubring ≤ O.toSubring) :
    ∃ V : ValuationSubring K, V ≤ O ∧ R ≤ V.toLocalSubring := by sorry
