-- Prove2me | Theorems.Thm_RoundedPotentials_Main_lemma_3_5
-- name    : RoundedPotentials.Main.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:34:57.64189+00:00
-- url     : https://prove2.me/theorems/52bb6670-8e45-4a9b-a2a6-974a5d61d301
-- title:
--   Lemma 3.5 — parameterized rounded potentials, both clauses
-- statement:
--   Let $r\le N$, $N\ge2$, $W\ge1$ be integers, and let the directed network on $r$ vertices have nonnegative integer capacities at most $W$. Put $Q=32N^2W$ and $\varepsilon_N=1/(8N)$.
--
--   For every feasible prescribed excess $b$, there is a vector $x\in[0,r-1]^V$ whose clipped assignment is capacity-feasible and realizes $b$ exactly. The rounded vector $\widehat x_v=\lfloor Qx_v\rfloor/Q$ is also capacity-feasible and satisfies
--   $$|\operatorname{ex}_{f^{\widehat x}}(v)-b_v|<\varepsilon_N,\qquad
--   0\le\lfloor Qx_v\rfloor\le(r-1)Q.$$
--   Each rounded index has at most $3\lfloor\log_2(NW)\rfloor+10$ binary digits.
--
--   For every $s\ne t$ and integer $p\ge0$,
--   $$\operatorname{MaxFlow}(s,t)=p\iff\exists i\in\mathbb Z^V:\quad
--   0\le i_v\le(2N-1)Q,\quad y=i/Q\text{ passes the interval, terminal and excess checks with parameter }N.$$
--   These certificate indices obey the same binary-length bound. Thus both the arbitrary-excess rounding statement and the terminal-pair characterization are included, with strict rounding error and non-strict certificate tolerance. For $r=0$ the first assertion is about the unique empty vector; for $r=1$ it includes the zero error case; neither case has distinct terminals.
--
--   Differences from the source:
--   - encoding: a finite vertex set V of size n → vertices Fin n and an edge list with distinct loopless ordered pairs; reason: relabeling preserves every flow and cut; m is the actual list length; zero capacities are explicitly allowed in §3
--   - encoding: MaxFlow(s,t) = p → IsGreatest of the set of real values of published IsFlow assignments; reason: records attainment without a real supremum default; the published definition has the same signed conservation equations
--   - reading: O(log(NW)) bits per grid index → binaryDigits ≤ 3 * Nat.log 2 (N * W) + 10; reason: the p.16 bound (2N−1)32N²W < 64(NW)³ implies this uniform explicit bound; one digit encodes zero
--   - encoding: W′ in Lemma 3.5 → W is the capacity bound of Instance r W; reason: only the symbol changes; N remains independent of the actual vertex count r
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), pp. 15–16, Lemma 3.5, eq. (10)

import Mathlib
import Definitions.Def_RoundedPotentials_Main_EnergyResidual

namespace RoundedPotentials.Main
open scoped BigOperators

theorem lemma_3_5 {r W : ℕ} (I : Instance r W) (hW : 1 ≤ W)
    (N : ℕ) (hN : 2 ≤ N) (hrN : r ≤ N) :
    (∀ b : Fin r → ℝ, (∃ g : Assignment r, CapacityFeasible I g ∧ HasExcess g b) →
      ∃ x : Fin r → ℝ,
        (∀ v, 0 ≤ x v ∧ x v ≤ (r : ℝ) - 1) ∧
        CapacityFeasible I (induced I x) ∧ HasExcess (induced I x) b ∧
        CapacityFeasible I (induced I (gridPotential N W (roundIndex N W x))) ∧
        (∀ v, |excess (induced I (gridPotential N W (roundIndex N W x))) v - b v| < epsilon N) ∧
        (∀ v, 0 ≤ roundIndex N W x v ∧
          roundIndex N W x v ≤ ((r : ℤ) - 1) * (denominator N W : ℤ) ∧
          binaryDigits (roundIndex N W x v) ≤ 3 * Nat.log 2 (N * W) + 10)) ∧
    (∀ (s t : Fin r), s ≠ t → ∀ p : ℤ, 0 ≤ p →
      (MaxValue I s t (p : ℝ) ↔ ∃ i : Fin r → ℤ,
        IndexRange N W i ∧ CertificateChecks I N s t p (gridPotential N W i) ∧
        ∀ v, binaryDigits (i v) ≤ 3 * Nat.log 2 (N * W) + 10)) := by sorry

end RoundedPotentials.Main
