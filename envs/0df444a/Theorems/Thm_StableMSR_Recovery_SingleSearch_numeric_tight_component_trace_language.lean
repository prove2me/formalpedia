-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleSearch_numeric_tight_component_trace_language
-- name    : StableMSR.Recovery.SingleSearch.numeric_tight_component_trace_language
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T20:19:26.916044+00:00
-- url     : https://prove2.me/theorems/da963c97-004c-4392-b5cc-e98ae6cc39c2
-- title:
--   Tight component table words realize singleton graph searches
-- statement:
--   Identify the vertices of a finite simple graph with precisely the active entries of a numeric array instance. Assume that array edges agree with graph adjacency between these entries. Use each vertex’s numeric label menu and the array’s directed compatibility test in the singleton separator search of width $w$. A word lists the successive pivot and label pairs. Its support is the set of these pairs after identifying active indices with vertices. Every accepted table word uses distinct pivot vertices and has support accepted by the graph search. Conversely every accepted graph output is the support of a table word. Thus
--   $$\{\operatorname{supp}(t): t\text{ is a table word}\}=\{O:O\text{ is a singleton-search root output}\}.$$
--   The theorem allows empty graphs, empty menus, and repeated entries in a menu. Child and root order are preserved in the word but are forgotten by its support.
-- source:
--   Prove2Me, Exact Sum-of-Radii Clustering under Any Constant Stability, regional circuit correctness, https://prove2.me/theorems/99dbdc83-616a-4376-a6ef-50377501acbd. Definitions.Def_StableMSR_SingleVertexSearch, run and root, and Definitions.Def_StableMSR_TightComponentTrace, traces. This is the graph-combinatorial step of the regional language theorem.

import Definitions.Def_StableMSR_TightComponentTrace
import Definitions.Def_StableMSR_SingleVertexSearch
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit

theorem StableMSR.Recovery.SingleSearch.numeric_tight_component_trace_language
    {V : Type} [Fintype V] [DecidableEq V] (d : SingleCircuit.Instance) (ix : V → Fin d.n)
    (inj : Function.Injective ix) (G : SimpleGraph V)
    (active : ∀ i : Fin d.n, d.active i.val = true ↔ ∃ v, ix v = i)
    (edges : ∀ v z, d.edge (ix v).val (ix z).val = true ↔ G.Adj v z) (w : ℕ) :
    let dom := fun v => (d.menu (ix v).val).toFinset
    let test := fun v z a b => d.test (ix v).val (ix z).val a b = true
    let tag := fun t : V × ℕ => ((ix t.1).val, t.2)
    let accepts := SingleSearch.root G dom test w (fun _ => 0)
    (∀ t, TightLanguage.traces d w t → ∃ l : List (V × ℕ),
      l.map tag = t ∧ (l.map Prod.fst).Nodup ∧ accepts l.toFinset) ∧
    ∀ O, accepts O → ∃ l : List (V × ℕ), TightLanguage.traces d w (l.map tag) ∧ l.toFinset = O := by sorry
