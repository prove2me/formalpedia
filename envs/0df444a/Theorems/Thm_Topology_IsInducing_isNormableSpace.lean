-- Prove2me | Theorems.Thm_Topology_IsInducing_isNormableSpace
-- name    : Topology.IsInducing.isNormableSpace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:48:15.865075+00:00
-- url     : https://prove2.me/theorems/4530fff8-7fc5-4f57-b8da-9ed5825b0aa4
-- title:
--   Is Inducing: is Normable Space
-- statement:
--   The Is Inducing construction uses the is Normable Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion. Separately attributed Apache-2.0 Mathlib compatibility backport at commit 9d581dfff2e41de989072ea63abf3daf69311520; target API and same-field transport specializations are explicit in the checked statement.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_ImportCompatibility_Normability
set_option autoImplicit true
open Topology
variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

theorem Topology.IsInducing.isNormableSpace [h : IsNormableSpace 𝕜 F]
    [TopologicalSpace E] {f : E →ₗ[𝕜] F} (hf : IsInducing f) :
    IsNormableSpace 𝕜 E := by sorry
