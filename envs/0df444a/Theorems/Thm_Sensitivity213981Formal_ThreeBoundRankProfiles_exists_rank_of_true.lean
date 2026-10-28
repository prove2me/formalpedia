-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankProfiles_exists_rank_of_true
-- name    : Sensitivity213981Formal.ThreeBoundRankProfiles.exists_rank_of_true
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:39:38.56383+00:00
-- url     : https://prove2.me/theorems/41107e09-d0c9-4a3a-ba44-26292b611f23
-- title:
--   exists rank of true — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \forall n:\mathbb N,\quad \forall I:\mathcal U,\quad \bigl[\mathrm{finite}(I)\bigr]\;\forall F:\left(\{0,\ldots,n-1\}\to \left(\left(I\to \mathbb B\right)\to \mathbb B\right)\right),\quad \bigl(\operatorname{Profiles.Nested}\bigl(F\bigr)\Longrightarrow \forall x:\left(I\to \mathbb B\right),\quad \forall g:\{0,\ldots,n-1\},\quad \bigl(\bigl(F\bigl(g, x\bigr) = \mathsf{true}\bigr)\Longrightarrow \exists r:\{0,\ldots,n-1\},\quad \bigl(\operatorname{RankProfiles.RankState}\bigl(F, x, r\bigr) \land \bigl(g \le r\bigr)\bigr)\bigr)\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding exists rank of true step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankProfileBounds.lean, lines 21–37.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RankProfileBounds
import Definitions.Def_Sensitivity213981Formal_Supplement_MinmaxLocal
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundRankProfiles.exists_rank_of_true :
∀ {n : Nat} {I : Type} [Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (x : I → Bool) (g : Fin n) (hg : @Eq.{1} Bool (F g x) Bool.true),
  @Exists.{1} (Fin n) fun (r : Fin n) =>
    And (@Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F x r) (@LE.le.{0} (Fin n) (@instLEFin n) g r) := by sorry
