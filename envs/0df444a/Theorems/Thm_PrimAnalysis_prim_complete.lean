-- Prove2me | Theorems.Thm_PrimAnalysis_prim_complete
-- name    : PrimAnalysis.prim_complete
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T01:15:31.544433+00:00
-- url     : https://prove2.me/theorems/e62ec6f7-85da-466f-b0a2-0fcb4091eb81
-- title:
--   Prim: correctness and running time for a reusable queue interface
-- statement:
--   For a represented connected undirected graph with signed integer weights, a valid root, an empty represented priority queue with sufficient capacity, and separate initialized key/parent/selected sequences, the compiled generic Prim call terminates and returns a minimum spanning parent sequence. The independently stated queue contracts supply the only queue assumptions. The same Call preserves the graph and all storage in the saved caller snapshot, returns the supplied parent reference, and satisfies OperationCounts. With initial queue potential Φ, per-update budget U, per-pop budget P, V vertices and E stored adjacency occurrences, backend-weighted work W satisfies W ≤ Φ + U(E+1) + PV. These are explicit source events; the bound does not count every machine instruction. CLRS fourth edition, Chapter 21, §21.2.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/prim.lean#L195-L313

import Definitions.Def_Algo_prim_prim_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem PrimAnalysis.prim_complete :
    ∀ {dependencies : Algo.prim.prim.Dependencies} {client : PrimAnalysis.Client}
      (model : PriorityQueueAnalysis.Model dependencies.PriorityQueue client.queue client.protection),
      PriorityQueueAnalysis.Contracts model PrimAnalysis.reservedClocks →
        LE.le.{0} client.size model.capacity →
          ∀ (before : PrimAnalysis.QueueState model),
            PrimAnalysis.Storage model before →
              Eq.{1} (PrimAnalysis.QueueState.entries model before) List.nil.{0} →
                (Eq.{1} (before.heap.read client.key) fun x => (0 : Int)) →
                  (Eq.{1} (before.heap.read client.parent) fun x => (-1 : Int)) →
                    (Eq.{1} (before.heap.read client.selected) fun x => (0 : Int)) →
                      LE.le.{0} (0 : Int) client.root →
                        LT.lt.{0} client.root client.size →
                          PrimGraph.Symmetric client.size client.adjacency →
                            Algo2Lean.Kruskal.ConnectedOn client.size.toNat
                                (PrimGraph.inputEdges client.size client.adjacency) →
                              Exists.{1} fun after =>
                                Algo.prim.prim.prim.Call dependencies before.heap
                                    (Prod.mk.{0, 0} client.graph
                                      (Prod.mk.{0, 0} client.root
                                        (Prod.mk.{0, 0} client.queue
                                          (Prod.mk.{0, 0} client.key
                                            (Prod.mk.{0, 0} client.parent client.selected)))))
                                    after client.parent ∧
                                  PrimGraph.GraphRep after client.graph client.size client.heads
                                      client.adjacency ∧
                                    PrimAnalysis.MinimumSpanningParents client.size client.adjacency
                                        client.root (after.read client.parent) ∧
                                      PrimAnalysis.OperationCounts before.heap after client.size.toNat
                                          (Algo2Lean.Dijkstra.edgeBudget client.adjacency
                                            (Algo2Lean.Dijkstra.vertexRange client.size)) ∧
                                        LE.le.{0} (PrimAnalysis.work model before.heap after)
                                            (HAdd.hAdd.{0, 0, 0}
                                              (HAdd.hAdd.{0, 0, 0}
                                                (PrimAnalysis.QueueState.potential model before)
                                                (HMul.hMul.{0, 0, 0} model.updateBudget
                                                  (HAdd.hAdd.{0, 0, 0}
                                                    (Algo2Lean.Dijkstra.edgeBudget client.adjacency
                                                      (Algo2Lean.Dijkstra.vertexRange client.size))
                                                    (1 : Nat))))
                                              (HMul.hMul.{0, 0, 0} model.popBudget client.size.toNat)) ∧
                                          LT.lt.{0} client.parent after.nextRef ∧
                                            client.caller.Footprint after List.nil.{0} List.nil.{0}
                                              List.nil.{0} := by
  sorry
