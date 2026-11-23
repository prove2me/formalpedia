-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleCircuit_regional_compiler_trace_language
-- name    : StableMSR.Recovery.SingleCircuit.regional_compiler_trace_language
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T20:19:30.41054+00:00
-- url     : https://prove2.me/theorems/0d59beea-6d03-4ab3-a038-26a7c4343d10
-- title:
--   The ordered-word language of the executable regional circuit
-- statement:
--   Fix a numeric instance, a width bound and an output point universe. A table word lists the pivot and its chosen label every time an alternative is taken, in component traversal order. Let $E(v,c)$ be the concatenation of the mask words owned by that choice. For the actual gate array and root address $(g,p)$ produced by the imperative compiler, the address lies in the array and
--   $$\mathcal L(g,p)=\{ E(t_1)\cdots E(t_k): (t_1,\ldots,t_k)\text{ is a table word}\}.$$
--   This includes empty root lists, rejected alternatives and missing component entries. No graph or metric assumptions on the input arrays are required.
-- source:
--   Prove2Me, Exact Sum-of-Radii Clustering under Any Constant Stability, regional circuit correctness, https://prove2.me/theorems/99dbdc83-616a-4376-a6ef-50377501acbd. Definitions.Def_StableMSR_SingleSeparatorCircuit, compileRegion and Language, and Definitions.Def_StableMSR_TightComponentTrace, traces.

import Definitions.Def_StableMSR_TightComponentTrace
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit

theorem StableMSR.Recovery.SingleCircuit.regional_compiler_trace_language (n : ℕ) (d : Instance) (w : ℕ) :
    let out := compileRegion d w
    let emit := fun m : List ℕ => WindowMasks.emit (Finset.univ.filter (fun i : Point n => m.contains i.val))
    let output := fun t : ℕ × ℕ => (d.owned t.1 t.2).flatMap emit
    out.2 < out.1.size ∧ ∀ s, Language n out.1 out.2 s ↔
      ∃ t, TightLanguage.traces d w t ∧ s = t.flatMap output := by sorry
