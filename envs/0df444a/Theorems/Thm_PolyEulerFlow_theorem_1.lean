-- Prove2me | Theorems.Thm_PolyEulerFlow_theorem_1
-- name    : PolyEulerFlow.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:05.765517+00:00
-- url     : https://prove2.me/theorems/760afae2-cc71-418e-8c5d-19a84e2b0fa3
-- title:
--   Theorem 1 — a common polynomial realization of a two-stack decider
-- statement:
--   Let $M$ be a deterministic two-stack decider. There are rational polynomial maps $F_M(h,z)$ and $c_M(x,h)$ on $\mathbb R^N$, a compact box $B=[lo,hi]$, an output coordinate $o$, four clock coordinates $p_0,\dots,p_3$, a compiled dyadic two-stack program $P$ of $M$ with some overhead $a$, an embedding of the data registers of $P$ into the coordinates, and constants $C,C',C_{len},r^*>0$, $0<c_-\le c_+$ and $c_1,C_{bits}\in\mathbb N$, all fixed by $M$, such that, with $K=256$, the following holds for every $T(n)\ge1$ bounding the transitions and every $H(n)\ge n$ bounding the stack heights of $M$ on inputs of binary length $n$, every input $x\in\mathbb N$ with $n=\ell(x)$, and every integer
--   $$s\ge C\big(1+n+H(n)+\log_2(T(n)+2)\big),\qquad h=2^{-s}.\tag{2}$$
--
--   1. **Euler executions.** Every execution $z_0=c_M(x,h)$, $z_{k+1}=z_k+\eta_kF_M(h,z_k)+\eta_k\xi_k$ with $0<\eta_k\le1$, $\sum_k\eta_k=\infty$, $\|\xi_k\|_\infty\le h^{2K}$ stays in $B$; at every physical time $t_k=\sum_{i<k}\eta_i\ge C's(T(n)+s)$ its output $z_k(o)$ is within $1/4$ of $1$ if $M$ accepts $x$ and of $0$ otherwise; its active length up to the first grid point at or beyond that horizon is at most $C_{len}s(T(n)+s)$; all its phase entries exist, and at every section $4j$, $j\in\mathbb N$, its data are within $r^*h$ (sup norm) of the encoding of the $j$-th configuration of $P$ on $x$ at scale $h$, consecutive sections being between $c_-(1+s)$ and $c_+(1+s)$ apart.
--   2. **Forced flow.** For every measurable forcing $\xi$ with $\|\xi(t)\|_\infty\le h^{2K}$ almost everywhere, a solution of $z(t)=c_M(x,h)+\int_0^t(F_M(h,z)+\xi)$ on $[0,\infty)$ exists, and every such solution stays in $B$, has the same decision bound for $t\ge C's(T(n)+s)$, has arc length $\int_0^{C's(T(n)+s)}\|F_M(h,z)+\xi\|_\infty\le C_{len}s(T(n)+s)$, has all its continuous phase entries $\theta_j$ (every fourth successive crossing of the clock threshold $9/10$), with the same section bound and gaps at $\theta_{4j}$, and $\theta_{4j}$ is the limit as $\eta\to0^+$ of the $4j$-th Euler phase-entry time of the constant-mesh-$\eta$ execution whose disturbances are the cell averages of $\xi$.
--   3. **Implementation.** Every unit-step orbit rounded to $b=2Ks+3$ fractional bits is an execution of item 1 (unit mesh, a permitted disturbance); the coordinates of $c_M(x,h)$, of every rounded state, and the value at $(h,w_k)$ of every monomial of $F_M$ are rationals of bit length at most $C_{bits}s$; and $C's(T(n)+s)\le2^{c_1s}$.
--
--   The field receives neither $T$ nor $H$: one fixed polynomial dynamics computes $M$ at unit step, at every Euler mesh and along the forced flow, with explicit time, length and precision bounds.
--
--   Differences from the source:
--   - reading: the encoded configurations of the compiled two-stack program (not specified) → an existential dyadic program P with CompilesTo P M a, fixed by M; reason: the proof (p.43) describes it only as the raw reader of Lemma 24 followed by the word program, with at most a(T(n)+s+n+1) transitions; CompilesTo states exactly this, so the paper's P satisfies it
--   - reading: a deterministic two-stack decider with finite control; integer input in canonical binary, 0 as one bit → transitions read both tops and pop-then-push a word per stack; the binary word MSB first on stack 1; reason: the paper fixes no instruction format; this one contains the one-operation machines
--   - reading: internal cycle sections; 'before and after the resetting halt' → every fourth strict first crossing of 9/10 by the clock coordinates, existence and the bounds asserted for every j ∈ ℕ; reason: §6.5, Lemma 16; P's run is constant after its halt
--   - reading: O(s(T(n)+s)) active length; Θ(1+s) gaps; 'the same section and resource guarantees hold for the continuous system' → explicit constants C_len, c₋, c₊ fixed by M, the same for the discrete and continuous clauses; continuous length = ∫‖F + ξ‖∞; reason: p.44: 'the same estimate on the speed gives the corresponding continuous bound'
--   - reading: its solution (the absolutely continuous solution) → a continuous solution of the integral equation on [0, ∞): existence asserted, every clause for every solution; reason: absolutely continuous solutions are these
--   - reading: limits of the constant-mesh Euler sections with cell-averaged disturbances → Tendsto along η → 0⁺ of η times the 4j-th phase-entry index; reason: the limit over the whole family of meshes (Lemma 16)
--   - reading: an implementation using O(s) fractional bits and O(s) workspace → the 2Ks+3-bit rounded unit-step orbits are executions; all their numbers have bit length ≤ C_bits s; the horizon is ≤ 2^{c₁s}; reason: the proof (p.44) justifies the claim by exactly these bit lengths and the 2^{c₁s} counter; no machine model of workspace is stated
--   - reading: an integer K ≥ 256; one may take K = 256 for every M → K = 256; reason: the paper's own choice, the strongest (largest disturbance h^{512})
--   - reading: its output is within 1/4 of the answer of M on x → |z(o) − 1| ≤ 1/4 if M accepts x, |z(o)| ≤ 1/4 if it rejects, at a fixed coordinate o; reason: the decision semantics of §2
--   - encoding: binary length n; log₂ → n = max(1, Nat.size x); Real.logb 2; reason: ℓ(0) = 1 (p.5)
--   - encoding: fixed compact box B; data registers → B = [lo, hi] coordinatewise; the data are the coordinates given by an injective map from P's encoding coordinates; reason: a compact box in ℝ^N; the field's data registers hold the encoded configuration
--   - generalization: H(n) ≥ n bounds each stack height, including the initial word and its fixed encoding overhead → H(n) ≥ n bounds both stacks of M (initial word included) at every step up to the halt, with no requirement to cover the encoding overhead; reason: every H the page allows bounds M's own heights, so it satisfies the Lean hypothesis; the overhead is a fixed factor (p.43: height at most a(H(n) + n + 1)) absorbed by the scale constant C
--   - encoding: only active coordinates are perturbed; the input and scale are exact and frozen → x and h are parameters of F and c, not coordinates of z, and every coordinate of z may be disturbed; reason: the frozen coordinates of the page are exactly the parameters (R10); no instance changes
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Theorem 1, p.2 (PDF 4–5)

import Mathlib
import Definitions.Def_PolyEulerFlow_CompilesTo
import Definitions.Def_PolyEulerFlow_fieldEval
import Definitions.Def_PolyEulerFlow_IsForcedSolution

open Filter Topology

namespace PolyEulerFlow

open Classical in
/-- **Theorem 1 (A common polynomial realization)**, p.2 (PDF 4–5). Bournez, One Polynomial Field for Every Euler Step and the
Flow (manuscript, sha256 c4e01b2b…).

For every deterministic two-stack decider `M` there are rational polynomial maps `F(h, z)`, `c(x, h)` on `ℝ^N`, a box `[lo, hi]`, an output
coordinate `o`, four clock coordinates `p`, a compiled dyadic two-stack program `P` of `M` (`CompilesTo P M a`), data coordinates `dataIdx`, and
constants, all fixed by `M`, such that, with `K = 256`, for every time bound `T`, height bound `H`, input `x` and scale `s` above (2), `h = 2^{-s}`:
(a) every execution with an admissible mesh and disturbances `‖ξ_k‖ ≤ h^{2K}` stays in the box, decides after `C′s(T(n)+s)`, has active length
`≤ C_len s(T(n)+s)` through the first grid point beyond that horizon, has all its phase entries, and at every section `4j` its data are within `r∗h`
of the encoding of the `j`-th configuration of `P`, with gaps in `[c₋(1+s), c₊(1+s)]`; (b) for every measurable forcing bounded by `h^{2K}` a.e. a
forced solution exists, and every forced solution satisfies the same box, decision, arc-length, section and gap bounds at its intrinsic
phase entries `θ_{4j}`, which are the limits of the constant-mesh Euler sections with cell-averaged disturbances; (c) unit-step orbits rounded to
`2Ks + 3` fractional bits are executions of (a), all their numbers have bit length `≤ C_bits s`, and the horizon is at most `2^{c₁s}`.

**Formalization Note** Readings R1–R12 of the mission: the quantifier order puts every object and constant before `T`, `H`, `x`, `s`, the mesh and the
disturbance; the compiled program is existential and linked to `M` by `CompilesTo`; sections are every fourth strict first crossing of `9/10`;
forced solutions are continuous solutions of the integral equation on `[0, ∞)`; the implementation clause is stated through bit lengths. -/
theorem theorem_1 (M : TwoStackDecider) (hM : M.IsDecider) :
    ∃ (N : ℕ) (F : Fin N → MvPolynomial (Option (Fin N)) ℚ) (c : Fin N → MvPolynomial (Fin 2) ℚ)
      (lo hi : Fin N → ℝ) (o : Fin N) (p : Fin 4 → Fin N)
      (P : DyadicProgram) (a : ℕ) (dataIdx : Fin P.c ⊕ Fin 4 → Fin N)
      (Cscale C' Clen rstar cm cp : ℝ) (c1 Cbits : ℕ),
      CompilesTo P M a ∧ Function.Injective dataIdx ∧
      0 < Cscale ∧ 0 < C' ∧ 0 < Clen ∧ 0 < rstar ∧ 0 < cm ∧ cm ≤ cp ∧ lo ≤ hi ∧
      ∀ (T H : ℕ → ℕ), M.BoundsTime T → M.BoundsHeight H →
      ∀ (x s : ℕ),
        Cscale * (1 + (inputLength x : ℝ) + (H (inputLength x) : ℝ)
          + Real.logb 2 ((T (inputLength x) : ℝ) + 2)) ≤ (s : ℝ) →
        let n := inputLength x
        let h := scale s
        let K : ℕ := 256
        let ν : ℝ := h ^ (2 * K)
        let f := fieldEval F h
        let z0 := initEval c x h
        let horizon : ℝ := C' * s * ((T n : ℝ) + s)
        let lenBound : ℝ := Clen * s * ((T n : ℝ) + s)
        let ans : ℝ := if M.Accepts x then 1 else 0
        let pv : Fin 4 → (Fin N → ℝ) → ℝ := fun i w => w (p i)
        let data : (Fin N → ℝ) → Fin P.c ⊕ Fin 4 → ℝ := fun w i => w (dataIdx i)
        let target : ℕ → Fin P.c ⊕ Fin 4 → ℝ := fun j => P.enc (P.conf x h j)
        -- (a) every execution at every admissible mesh
        (∀ (η : ℕ → ℝ) (ξ : ℕ → Fin N → ℝ), IsAdmissibleMesh η → IsPermittedDisturbance ν ξ →
          let z := eulerOrbit f z0 η ξ
          let t := physTime η
          (∀ k, z k ∈ Set.Icc lo hi) ∧
          (∀ k, horizon ≤ t k → |z k o - ans| ≤ 1 / 4) ∧
          activeLengthOn z 0 (firstGrid η horizon) ≤ lenBound ∧
          ∃ kk : ℕ → ℕ, IsPhaseEntries pv z 0 kk ∧
            ∀ j : ℕ, ‖data (z (kk (4 * j))) - target j‖ ≤ rstar * h ∧
              cm * (1 + s) ≤ t (kk (4 * (j + 1))) - t (kk (4 * j)) ∧
              t (kk (4 * (j + 1))) - t (kk (4 * j)) ≤ cp * (1 + s)) ∧
        -- (b) the continuous system with every measurable forcing
        (∀ ξ : ℝ → Fin N → ℝ, IsPermittedForcing ν ξ →
          (∃ z : ℝ → Fin N → ℝ, IsForcedSolution f z0 ξ z) ∧
          ∀ z : ℝ → Fin N → ℝ, IsForcedSolution f z0 ξ z →
            let θ := contPhaseEntry pv z
            (∀ τ, 0 ≤ τ → z τ ∈ Set.Icc lo hi) ∧
            (∀ τ, horizon ≤ τ → |z τ o - ans| ≤ 1 / 4) ∧
            ∫ u in (0 : ℝ)..horizon, ‖f (z u) + ξ u‖ ≤ lenBound ∧
            ContPhaseEntriesExist pv z ∧
            ∀ j : ℕ, ‖data (z (θ (4 * j))) - target j‖ ≤ rstar * h ∧
              cm * (1 + s) ≤ θ (4 * (j + 1)) - θ (4 * j) ∧
              θ (4 * (j + 1)) - θ (4 * j) ≤ cp * (1 + s) ∧
              Tendsto (cellEulerEntryTime pv f z0 ξ (4 * j)) (𝓝[>] 0) (𝓝 (θ (4 * j)))) ∧
        -- (c) the unit-step implementation with `2Ks + 3` fractional bits
        (∀ w : ℕ → Fin N → ℝ, IsRoundedOrbit f z0 (2 * K * s + 3) w →
          (∃ ξ : ℕ → Fin N → ℝ, IsPermittedDisturbance ν ξ ∧ w = eulerOrbit f z0 (fun _ => 1) ξ) ∧
          (∀ i, HasBitLengthLE (z0 i) (Cbits * s)) ∧
          (∀ k i, HasBitLengthLE (w k i) (Cbits * s)) ∧
          (∀ k i, ∀ d ∈ (F i).support,
            HasBitLengthLE
              (MvPolynomial.aeval (fun v : Option (Fin N) => v.elim h (w k))
                (MvPolynomial.monomial d ((F i).coeff d))) (Cbits * s))) ∧
        horizon ≤ (2 : ℝ) ^ (c1 * s) := by sorry

end PolyEulerFlow
