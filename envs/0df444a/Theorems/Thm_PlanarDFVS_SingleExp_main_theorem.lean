-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_main_theorem
-- name    : PlanarDFVS.SingleExp.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:53.080613+00:00
-- url     : https://prove2.me/theorems/0190f3f5-7268-4e7e-b36d-01b2172c8d95
-- title:
--   Theorem 1.1 — single-exponential randomized and deterministic algorithms
-- statement:
--   Let $D$ be any planar directed multigraph with $n$ vertices and let $k\in\mathbb N$. Loops, disconnected graphs, parallel arcs and antiparallel arcs are allowed; no embedding or optimum is supplied. Set $N=\max(1,n)$ and let $\ell$ be the encoded input length.
--
--   There exist one uniform randomized program $R$ and one uniform deterministic program $D$, positive absolute constants $C_R,C_D,S_R,S_D$, and fixed natural exponents $d_R,d_D,e_R,e_D$, all chosen before every instance, such that
--
--   $$T_R\le C_R(2+\sqrt5)^kN^{d_R}\le C_R(4.2361)^kN^{d_R},\qquad T_D\le C_D(8.03)^kN^{d_D},$$
--   $$\operatorname{space}_R\le S_R\ell^{e_R},\qquad \operatorname{space}_D\le S_D\ell^{e_D}.$$
--
--   The randomized program always returns a valid size-at-most-$k$ DFVS or Fail and succeeds with probability at least $1/2$ on every yes-instance. The deterministic program succeeds exactly on yes-instances. All finite graph instances and all budgets are included, with empty graphs and $k\ge n$ handled by the same uniform programs. This is the full conjunction of both algorithms and both polynomial-space clauses, with the printed numerical comparison retained.
--
--   Differences from the source:
--   - reading: algorithms and polynomial factors with elementary operations and serialization unspecified → one finite binary instruction program, charged bit operations, fixed positive coefficients and natural degrees before every input; reason: retains uniform asymptotic resources with an operational program; no cost certificate or assumed fast optimizer
--   - reading: n is the number of vertices; digraphs may have arbitrarily many duplicate arcs → DFVS input is n, binary k and the n by n directed support bits, including loops; reason: all multigraph instances have the same cycle and DFVS answers as their support; explicit duplicate-list reading has an additional reading cost and is not claimed here
--   - encoding: polynomial space and bounded randomized running time → maximum live workspace along every finite-prefix execution, common halting horizon per input, independent fair bits with charged sampling; reason: the bit prefixes define the law semantically without materializing support; bounded rejection with a Fail outcome and amplification can preserve one-sided success at least 1/2
--   - encoding: n to an unspecified fixed polynomial power → max(1,n) to a fixed natural degree; reason: includes n=0 without a vanishing upper bound; changes no asymptotic claim
--   - encoding: decimal constants 8.03 and 4.2361 → exact rationals 803/100 and 42361/10000; reason: the numbered headline and Theorem 5.2 determine 8.03 despite the abstract typo; no exponential base is weakened
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 2 (PDF p. 2), Theorem 1.1 (main theorem), with Theorem 4.2 one-sided guarantee

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp

theorem main_theorem :
    ∃ (R D : Program) (CR CD SR SD : ℝ) (dR dD eR eD : ℕ),
      0 < CR ∧ 0 < CD ∧ 0 < SR ∧ 0 < SD ∧
      RandomGuarantee R (2 + Real.sqrt 5) CR dR SR eR ∧
      DeterministicGuarantee D (803 / 100) CD dD SD eD ∧
      (∀ k n : ℕ,
        CR * (2 + Real.sqrt 5)^k * (max 1 n : ℕ)^dR ≤
          CR * (42361 / 10000 : ℝ)^k * (max 1 n : ℕ)^dR) := by sorry

end PlanarDFVS.SingleExp
