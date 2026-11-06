-- Prove2me | Theorems.Thm_SparsificationLemma_Sketch_clauses_le
-- name    : SparsificationLemma.Sketch.clauses_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:13.825622+00:00
-- url     : https://prove2.me/theorems/187fcea7-a82e-45dc-bdc2-c979256abb5e
-- title:
--   Sketch: clauses le
-- statement:
--   «and each has at most (M(ε)+2)n clauses, as there are only 2n clauses with one literal.» For
--   thresholds with `ThrC`, 1 ≤ k, 1 ≤ τ, paths cut after at least (β 0 + … + β (k−1))·n steps, and 2·(θ
--   0 + … + θ (k−1)) as M(ε):
--   the formula at a leaf has at most M(ε)·n clauses, the side list, every clause written once, at most
--   2n, and the output at most (M(ε)+2)·n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Sketch.lean#L54-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Sketch.lean#L54-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_StepSparsifyDefs
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_SparsificationLemma_Nodes
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_ClauseBoundStatement
import Definitions.Def_CountKSatStatement
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_SparsificationLemma_Sketch
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Sketch
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK

theorem SparsificationLemma.Sketch.clauses_le {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml} (hk : 1 ≤ k) (hτ : 1 ≤ τ) (hT : ThrC k τ θ β) (hD : (∑ i ∈ range k, β i) * n ≤ D) (hψ : IsKCNF k n ψ) :
    ∀ x ∈ tree θ k D ψ, x.1.length ≤ (2 * ∑ j ∈ range k, θ j) * n ∧ (sideU x.2).length ≤ 2 * n ∧ (out x).length ≤ (2 * (∑ j ∈ range k, θ j) + 2) * n := by sorry
