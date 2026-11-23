-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleSearch_numeric_tight_table_row
-- name    : StableMSR.Recovery.SingleSearch.numeric_tight_table_row
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-23T20:27:37.169737+00:00
-- url     : https://prove2.me/theorems/48236ae4-3cf7-4b3a-ad9b-1419dfbf54fe
-- title:
--   Exact language of a tight component table entry
-- statement:
--   Let $C$ be a nonempty component after deletion of its own exterior boundary $S$ in a finite indexed graph. Assume $|S|\leq w$ and that every prescribed boundary label belongs to its vertex menu. For every search depth $m\geq |C|$, query the completed table by the increasing vertex indices of $C$ and the prescribed labels on the increasing indices of $S$. A missing key is interpreted as the empty language. Every accepted word lists each vertex of $C$ exactly once and its labelled support is a valid singleton-search output with that boundary. Conversely every such output is the support of a word accepted at this key. The claim applies to all tight interior components, with arbitrary legal numeric boundary labels.
-- source:
--   Prove2Me, Exact Sum-of-Radii Clustering under Any Constant Stability, regional circuit correctness, https://prove2.me/theorems/99dbdc83-616a-4376-a6ef-50377501acbd. Definitions.Def_StableMSR_TightComponentTrace, build, lookup and wordAlgebra, and Definitions.Def_StableMSR_SingleVertexSearch, run. This is the interior induction statement for https://prove2.me/theorems/da963c97-004c-4392-b5cc-e98ae6cc39c2 .

import Definitions.Def_StableMSR_TightComponentTrace
import Definitions.Def_StableMSR_SingleVertexSearch
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit

theorem StableMSR.Recovery.SingleSearch.numeric_tight_table_row
    {V : Type} [Fintype V] [DecidableEq V] (d : SingleCircuit.Instance) (ix : V → Fin d.n)
    (inj : Function.Injective ix) (G : SimpleGraph V)
    (active : ∀ i : Fin d.n, d.active i.val = true ↔ ∃ v, ix v = i)
    (edges : ∀ v z, d.edge (ix v).val (ix z).val = true ↔ G.Adj v z)
    (w m : ℕ) (C : Finset V) (a : ℕ → ℕ)
    (flap : Havens.IsFlap G (DecompositionSearch.boundary G C) C)
    (space : (DecompositionSearch.boundary G C).card ≤ w) (depth : C.card ≤ m)
    (valid : ∀ v ∈ DecompositionSearch.boundary G C, a (ix v).val ∈ d.menu (ix v).val) :
    let code := fun K : Finset V => (K.image (fun v => (ix v).val)).sort (· ≤ ·)
    let S := DecompositionSearch.boundary G C
    let key := (code S).map (fun j => (j,a j))
    let table := (TightLanguage.build TightLanguage.wordAlgebra d w).2
    let accepts := (TightLanguage.lookup table (code C) key).getD (fun _ => False)
    let dom := fun v => (d.menu (ix v).val).toFinset
    let test := fun v z c k => d.test (ix v).val (ix z).val c k = true
    let tag := fun t : V × ℕ => ((ix t.1).val,t.2)
    let runs := SingleSearch.run G dom test w m S C (fun v => a (ix v).val)
    (∀ t, accepts t → ∃ l : List (V × ℕ), l.map tag = t ∧ (l.map Prod.fst).Nodup ∧
      (l.map Prod.fst).toFinset = C ∧ runs l.toFinset) ∧
    ∀ O, runs O → ∃ l : List (V × ℕ), accepts (l.map tag) ∧ l.toFinset = O := by sorry
