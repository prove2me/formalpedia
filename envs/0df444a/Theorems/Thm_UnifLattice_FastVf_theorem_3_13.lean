-- Prove2me | Theorems.Thm_UnifLattice_FastVf_theorem_3_13
-- name    : UnifLattice.FastVf.theorem_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:21:10.653695+00:00
-- url     : https://prove2.me/theorems/1627149a-aa30-48fa-97c4-801ce790a07c
-- title:
--   Theorem 3.13 — V_f = Ver^q(pp, f) is computable in polynomial time from an ordered read-once branching program for the wiring function
-- statement:
--   **Theorem 3.13 (Fast Computation of $V_f$).** Let $m,q\in\mathbb N$ be lattice parameters, $L=2^\ell$ for an integer $\ell\ge0$, and $f$ a quadratic function with wiring function $g:[L]^3\to\{-1,0,1\}$. Suppose $g$ is computed by an ordered read-once branching program $BP_g=(\pi,\{M_{\tau,b}\}_{\tau\in[3\ell],b\in\{0,1\}},s,t)$ of width $w$. Then there is an algorithm that takes as input $pp=(W,V)$, $W,V\in\{0,1\}^{m\times2m^3}$, together with $BP_g$, and outputs
--   $$V_f=\mathrm{Ver}^q(pp,f)=\sum_{i,j,k\in[L]}g(i,j,k)\,(I_m\otimes\mathrm{vec}(V_i))\,V_j\,\widehat W_k\in\mathbb Z^{m^3\times m}$$
--   in time $\mathrm{poly}(m,w,\ell,\log q)$.
--
--   This is the step that lets a verifier compute its verification matrix in time polylogarithmic in $L$ for layers whose wiring is given by small ordered branching programs; summing the $L^3$ terms directly takes time exponential in $\ell$.
--
--   **Formalization Note.** One function `alg : List Bool → List Bool` with `PolyTimeComputable alg` is fixed before $m$, $pp$ and the program; for every $m$, every $pp$ and every program `B` satisfying the Ordering clause, `alg (encInput m pp B) = encVf (verQ pp B.ℓ B.value)`. The input codes $m,\ell,w$ in unary and contain no object of size $L$, so polynomial time in the input length is $\mathrm{poly}(m,w,\ell)$; the output lists the integer entries of $V_f$ in binary. `verQ` is the $L^3$-term sum of Construction 3.8.
--
--   Differences from the source:
--   - generalization: time poly(m, w, ℓ, log q) → QAlgorithms.Complexity.PolyTimeComputable alg (time polynomial in the input length), q not an input; reason: the input length lies between max(m, w, ℓ) and a polynomial in m, w, ℓ, so polynomial time in it is poly(m, w, ℓ); a bound without log q implies the paper's
--   - generalization: f quadratic with wiring function g : [L]^3 → {−1,0,1}, g computed by the ordered read-once branching program BP_g; output V_f = Ver^q(pp, f) → every ordered program B (Ordering clause kept, Correctness dropped); output verQ pp B.ℓ B.value, V_f formed with the program's own value; reason: under the paper's hypotheses g = B.value by Correctness and Ver^q(pp, f) = verQ pp ℓ g, so the paper's statement is the special case
--   - encoding: an algorithm taking pp and BP_g as input and outputting V_f → a function alg : List Bool → List Bool with alg (encInput m pp B) = encVf V_f (the codes of the Encoding item: m, ℓ, w unary, bitwise matrices, signed binary output); reason: a fixed explicit bit-string interface; the deterministic algorithm of the paper is a function of its input
--   - encoding: indices in [L], [3ℓ]; W, V ∈ {0,1}^{m×2m^3}; V_f ∈ Z^{m^3×m} → 0-based Fin types, product index types with the paper's lexicographic flattening; reason: Lean convention; same objects
--   - generalization: m, w ∈ ℕ (lattice parameter, width) → every m, w : ℕ, including 0; reason: the degenerate instances are trivially included; every source instance is covered
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), p. 24, Theorem 3.13

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_UnifLattice_FastVf_VectorCommitment
import Definitions.Def_UnifLattice_FastVf_QuadraticCommitment
import Definitions.Def_UnifLattice_FastVf_ROBP
import Definitions.Def_UnifLattice_FastVf_Encoding

namespace UnifLattice.FastVf

/-- Theorem 3.13 (Fast Computation of `V_f`), p. 24: there is one polynomial-time algorithm that,
for every `m`, every `pp = (W, V)` with `W, V ∈ {0,1}^{m × 2m³}` and every ordered read-once
branching program `BP_g = (π, {M_{τ,b}}, s, t)` of width `w` over `3ℓ` bits, takes `pp` and `BP_g`
as input and outputs `V_f = Ver^q(pp, f) = Σ_{i,j,k ∈ [L]} g(i,j,k) (I_m ⊗ vec(V_i)) V_j Ŵ_k`
(`L = 2^ℓ`) for `g` the function computed by `BP_g`. Time is polynomial in the input length, which
lies between `max(m, w, ℓ)` and a polynomial in `m, w, ℓ`. -/
theorem theorem_3_13 :
    ∃ alg : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable alg ∧
      ∀ (m : ℕ) (pp : CommitParams m) (B : ROBP), B.Ordered →
        alg (encInput m pp B) = encVf (verQ pp B.ℓ B.value) := by sorry

end UnifLattice.FastVf
