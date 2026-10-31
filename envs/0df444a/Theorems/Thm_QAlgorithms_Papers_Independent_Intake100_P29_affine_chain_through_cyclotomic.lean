-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P29_affine_chain_through_cyclotomic
-- name    : QAlgorithms.Papers.Independent.Intake100.P29.affine_chain_through_cyclotomic
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:29:57.102469+00:00
-- url     : https://prove2.me/theorems/91be3d77-224d-4382-a6db-f9be8bb1cb98
-- title:
--   Affine linkage can stay among cyclotomic simple modules
-- statement:
--   Let $F$ be algebraically closed, $n,r\ge1$, $q\in F^\times\setminus\{1\}$, and $Q\in(F^\times)^r$. Write $H$ for the cyclotomic quotient of $\mathcal H_n^{\mathrm{aff}}$ defined by $\prod_a(X_1-Q_a)$. Let $D,D'$ be nonzero simple finite-dimensional right $H$-modules. Then
--
--   $$
--   D\sim_{\mathrm{block},\,\mathcal H_n^{\mathrm{aff}}}D'
--   \quad\Longleftrightarrow\quad
--   \exists\, D=D_1,D_2,\ldots,D_k=D'\quad
--   \forall i<k,\quad
--   \operatorname{Ext}^1_{\mathcal H_n^{\mathrm{aff}}}(D_i,D_{i+1})\ne0
--   \ \text{or}\
--   \operatorname{Ext}^1_{\mathcal H_n^{\mathrm{aff}}}(D_{i+1},D_i)\ne0,
--   $$
--
--   where every $D_i$ is a simple finite-dimensional $H$-module. Endpoints and chains are taken up to module isomorphism; a one-vertex chain is permitted. The middle modules of the affine extensions are arbitrary affine modules and need not be $H$-modules. This states the restricted-vertex form of the introduction's block theorem.
-- source:
--   Blocks of cyclotomic Hecke algebras, arXiv:math/0607451v4, PDF p. 2, Introduction Corollary

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P29

namespace QAlgorithms.Papers.Independent.Intake100.P29

noncomputable section

open scoped BigOperators Classical

variable {F : Type} [Field F]

/-- Introduction Corollary, PDF p. 2, inheriting p. 1's algebraically closed
nonzero-parameter setup. Vertices factor through H; the affine extension
middle terms need not. Reflexive linkage allows a one-vertex chain. -/
theorem affine_chain_through_cyclotomic [IsAlgClosed F] (m r : ℕ)
    (q : F) (hq : q ≠ 0) (hqOne : q ≠ 1) (Q : Fin (r + 1) → F) (hQ : ∀ a, Q a ≠ 0)
    (D Dprime : AffineModule F m q) (hD : Simple D) (hDprime : Simple Dprime)
    (hDQ : FactorsCyclotomic Q D) (hDprimeQ : FactorsCyclotomic Q Dprime) :
    Linkage (fun _ => True) (fun _ => True) D Dprime ↔
      Linkage (FactorsCyclotomic Q) (fun _ => True) D Dprime := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P29
