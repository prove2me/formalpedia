-- Prove2me | Theorems.Thm_PlanarDFVSKernel_theorem_1_1
-- name    : PlanarDFVSKernel.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:28.492255+00:00
-- url     : https://prove2.me/theorems/38e2d60d-5d84-4e8d-a52e-850808c84de9
-- title:
--   Theorem 1.1 — a deterministic polynomial kernel for Planar DFVS with $O(k^{66}\log^2k)$ vertices, arcs and parameter
-- statement:
--   **Theorem 1.1.** Planar Directed Feedback Vertex Set admits a deterministic kernel with $O(k^{66}\log^2k)$ vertices and arcs and output parameter $k'=O(k^{66}\log^2k)$.
--
--   Formally: there are a constant $c$ and a map $(D,k)\mapsto(D',k')$ on instances, computed by one deterministic Turing machine in time polynomial in the length of the input encoding (explicit vertex and arc lists, binary parameter), such that for every instance with $D$ planar,
--   1. $D'$ is planar;
--   2. $(D',k')$ is a YES-instance if and only if $(D,k)$ is;
--   3. $|V(D')|+|A(D')|\le c\,(k+2)^{66}\lfloor\log_2(k+2)\rfloor^2$;
--   4. $k'\le c\,(k+2)^{66}\lfloor\log_2(k+2)\rfloor^2$.
--
--   This settles the planar case of the polynomial-kernel question for Directed Feedback Vertex Set.
--
--   Differences from the source:
--   - encoding: a deterministic polynomial-time algorithm → one Mathlib TM2 machine (Turing.TM2ComputableInPolyTime) with input and output encoded by encInst (unary n, binary arc list and k); reason: polynomial time is model-robust; encInst is injective and matches the paper's encoding size
--   - encoding: O(k⁶⁶ log² k) → c·(k + 2)⁶⁶·⌊log₂(k + 2)⌋² with one c for all instances; reason: equal up to constants for k ≥ 2; a kernel bound must also cover k ≤ 1, where k⁶⁶ log² k = 0
--   - encoding: O(k⁶⁶ log² k) vertices and arcs → one bound on the number of vertices plus arcs; reason: equivalent to two separate bounds up to a factor 2
--   - encoding: PDFVS inputs are planar digraphs; the output is an instance of the same problem → the machine is total; the conclusions (including planarity of the output) are required for planar inputs; reason: PDFVS instances are exactly the planar ones
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Theorem 1.1, p.1 (PDF 2); proof §6.4, p.33 (PDF 34)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_PDFVSInstance

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Theorem 1.1** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Theorem 1.1, p.1 (PDF 2); proof §6.4, p.33 (PDF 34)):
"Planar Directed Feedback Vertex Set admits a deterministic kernel with O(k⁶⁶ log² k) vertices and
arcs and output parameter k′ = O(k⁶⁶ log² k)."

There are a constant `c` and a map `ker` on instances, computed by a (deterministic) Turing
machine in time polynomial in the length of the input encoding, such that for every instance
`(D, k)` with `D` planar the output `(D′, k′)` is planar, it is a YES-instance exactly when
`(D, k)` is, `|V(D′)| + |A(D′)| ≤ c (k + 2)⁶⁶ ⌊log₂(k + 2)⌋²` and `k′ ≤ c (k + 2)⁶⁶ ⌊log₂(k + 2)⌋²`.

**Formalization Note**
1. The machine is Mathlib's `Turing.TM2ComputableInPolyTime` (a deterministic multi-stack Turing
   machine with a polynomial time bound), one machine for all inputs, with input and output encoded
   by `encInst`: `n` in unary (explicit vertex list), the arc list and `k` in self-delimiting
   binary (p.8 (PDF 9): "explicit vertex and arc lists and a binary parameter"). `encInst` is
   injective.
2. `O(k⁶⁶ log² k)` is `c · (k + 2)⁶⁶ · ⌊log₂(k + 2)⌋²` with one `c` for every instance; for
   `k ≥ 2` it is within a constant factor of `k⁶⁶ log² k`, and a kernel's size bound must also
   hold at `k ∈ {0, 1}`, where `k⁶⁶ log² k = 0`.
3. Promise form: the conclusions are required for planar inputs (the domain of PDFVS); the machine
   is total. The input comes without an embedding. -/
theorem theorem_1_1 :
    ∃ c : ℕ, ∃ ker : PDFVSInstance → PDFVSInstance,
      Nonempty (Turing.TM2ComputableInPolyTime encInst encInst ker) ∧
      ∀ I : PDFVSInstance, Planar I.G →
        Planar (ker I).G ∧
        (Feasible I.G I.k ↔ Feasible (ker I).G (ker I).k) ∧
        (ker I).n + (ker I).m ≤ c * (I.k + 2) ^ 66 * Nat.log 2 (I.k + 2) ^ 2 ∧
        (ker I).k ≤ c * (I.k + 2) ^ 66 * Nat.log 2 (I.k + 2) ^ 2 := by sorry

end PlanarDFVSKernel
