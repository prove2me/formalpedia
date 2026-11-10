-- Prove2me | Theorems.Thm_SubspaceConv_transposition
-- name    : SubspaceConv.transposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:12.132682+00:00
-- url     : https://prove2.me/theorems/c940300b-d4a8-4dac-8b4d-41e854014549
-- title:
--   §3.3 — transposition principle: $\langle g,Pf\rangle=\langle P'g,f\rangle$ with cost $P'\le2\,\mathrm{cost}\,P+|\kappa|$
-- statement:
--   For every well-formed linear straight-line program $P$ with inputs $\iota$ and outputs $\kappa$ there is a well-formed linear straight-line program $P'$ with inputs $\kappa$ and outputs $\iota$ such that
--
--   1. $P'$ computes the transpose of $P$: for every commutative ring $A$, every value of $p^{-1}\in A$, and all tables $f:\iota\to A$, $g:\kappa\to A$,
--   $$\sum_{o\in\kappa}g(o)\,(Pf)(o)=\sum_{i\in\iota}(P'g)(i)\,f(i);$$
--   2. $\mathrm{cost}(P')\le2\,\mathrm{cost}(P)+|\kappa|$.
--
--   This is the paper's procedure: attach a zero accumulator to each wire, add each new input to the accumulator of its output wire, and traverse the gates backwards ($z=x+y$: $a_x\leftarrow a_x+a_z$, $a_y\leftarrow a_y+a_z$; $z=cx$: $a_x\leftarrow a_x+c\,a_z$); the accumulators on the original input wires give the transpose. Applied to a program for $Z_{n,k}$ it gives $Z_{n,k}^{\mathsf T}$, and applied to a program for $Z_{n,k}^{-1}$ it gives $(Z_{n,k}^{\mathsf T})^{-1}$, at the same asymptotic cost.
--
--   **Formalization Note** "The same asymptotic cost" is the explicit count in item 2: each arithmetic gate of $P$ becomes at most two operations, and each new input costs at most one addition into its output wire's accumulator.
--
--   Differences from the source:
--   - reading: "This computes Z^T_{n,k} with the same asymptotic cost" → cost(P′) ≤ 2·cost(P) + |κ|; reason: the count read off the printed procedure
--   - generalization: the circuit for Z_{n,k} (and its inverse), with gates z = x + y and z = cx → every well-formed linear straight-line program (add, sub, integer scaling, multiplication by p⁻¹, free inputs and zero), over every commutative ring and every value of p⁻¹; reason: the procedure applies gate by gate; the circuits for Z_{n,k} and Z_{n,k}^{−1} are instances
--   - encoding: "the accumulators on the original input wires give the transpose" → ∑_o g(o)(Pf)(o) = ∑_i (P′g)(i) f(i) for all f, g; reason: the defining property of the transpose of a linear map
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_SubspaceConv_LinSLP

universe u

namespace SubspaceConv

/-- **The transposition principle of §3.3**, Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, p.13 (PDF p.14): applied to a linear
circuit, the backward accumulator procedure ("Attach a zero accumulator `a_v` to each circuit wire
`v`. Add each new input to the accumulator of its corresponding output wire … Traverse gates
backwards: `z = x + y : a_x ← a_x + a_z, a_y ← a_y + a_z`, `z = cx : a_x ← a_x + c a_z`") computes
the transpose "with the same asymptotic cost".

**Formalization Note** For every well-formed linear straight-line program `P` from `ι` to `κ`
there is a well-formed program `P'` from `κ` to `ι` computing the transposed linear map,
`⟨g, P f⟩ = ⟨P' g, f⟩` for all tables `f`, `g`, over every commutative ring and every value of
`pinv` (the map is linear for each fixed `pinv`). "The same asymptotic cost" is the explicit
count `cost P' ≤ 2 cost P + |κ|`: every arithmetic gate of `P` becomes at most two operations,
and each new input is added into its output wire's accumulator (at most one addition each).
Applied to a program for `Z` it gives `Zᵀ`; applied to a program for `Z⁻¹` it gives `(Zᵀ)⁻¹`. -/
theorem transposition {ι κ : Type*} [Fintype ι] [Fintype κ] (P : LinSLP ι κ)
    (hP : P.WellFormed) :
    ∃ P' : LinSLP κ ι, P'.WellFormed ∧ P'.cost ≤ 2 * P.cost + Fintype.card κ ∧
      ∀ (A : Type u) [CommRing A] (pinv : A) (f : ι → A) (g : κ → A),
        ∑ o, g o * P.eval pinv f o = ∑ i, P'.eval pinv g i * f i := by sorry

end SubspaceConv
