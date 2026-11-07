-- Prove2me | Theorems.Thm_PopRAM_expected_time_B1
-- name    : PopRAM.expected_time_B1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:23:33.320199+00:00
-- url     : https://prove2.me/theorems/a14c6e4a-c373-4c74-8ed3-31655459aa66
-- title:
--   §B.1 display — $\mathbb E[\text{stabilisation time}]\le A+n^{-\eta}D(n)$ from a whp bound $A$ and a residual bound $D$
-- statement:
--   Consider any population protocol, initial configuration $c_0$ and set $S$ of configurations, and let $\tau_S$ be the hitting time of $S$. Suppose that, for some $A\in\mathbb N$ and $\varepsilon,D\in[0,\infty]$,
--
--   1. the run from $c_0$ hits $S$ within $A$ interactions except with probability at most $\varepsilon$: $\Pr_{c_0}[\tau_S>A]\le\varepsilon$, and
--   2. from every configuration $c$ reachable from $c_0$, $\mathbb E_c[\tau_S]\le D$.
--
--   Then
--   $$\mathbb E_{c_0}[\tau_S]\le A+\varepsilon D .$$
--
--   With $\varepsilon=n^{-\eta}$ and $D=D(n)=n^{O(1)}$ this is the paper's $\mathbb E[\text{stabilisation time}]\le A+n^{-\eta}D(n)=O(A)$, by choosing $\eta$ larger than the degree of $D$: the expected-time accounting by which the whp bound of the MC+ simulation becomes an expected bound.
--
--   Differences from the source:
--   - generalization: A a whp bound of the fast simulation, ε = n^{−η}, D(n) = n^{O(1)} the residual bound of the combined protocol → any protocol, target set, A ∈ ℕ, ε and D in [0, ∞]; reason: the paper's display is the instance ε = n^{−η}, D = D(n)
--   - encoding: expected time from a reachable configuration → lower Lebesgue integral of the hitting time of the run restarted at c with a fresh i.i.d. schedule; reason: the scheduler is memoryless
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), §B.1, display on p.20 (PDF p.21)

import Mathlib
import Definitions.Def_PopRAM_Protocol

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **§B.1, display on p.20** (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held version
sha256 f13223b3…, p.20, PDF p.21). "Consequently, if A = O(ρ′w + τ log n) is a high-probability
bound for successful completion of the fast simulation and D(n) = n^{O(1)} bounds the expected
remaining detection, switching, and backup time from any reachable configuration, then
E[stabilisation time] ≤ A + n^{−η}D(n) = O(A)."

For any protocol, initial configuration `c₀` and target set `S`: if the run from `c₀` hits `S`
within `A` interactions except with probability at most `ε`, and from every configuration reachable
from `c₀` the expected hitting time of `S` is at most `D`, then the expected hitting time of `S` from
`c₀` is at most `A + ε·D`.

**Formalization Note** The paper's display is the instance `ε = n^{-η}`, `D = D(n) = n^{O(1)}`; the
final `= O(A)` follows by choosing `η` larger than the degree of `D`. The expectation "from `c`" is
the run started at `c` with a fresh i.i.d. schedule. -/
theorem expected_time_B1 {Q : Type*} {n : ℕ} (δ : Q → Q → Q × Q) (c₀ : Fin n → Q)
    (S : Set (Fin n → Q)) (A : ℕ) (ε D : ℝ≥0∞)
    (hA : sched n {ω | (A : ℕ∞) < hit δ c₀ S ω} ≤ ε)
    (hD : ∀ c, Reachable δ c₀ c → ∫⁻ ω, (hit δ c S ω : ℝ≥0∞) ∂(sched n) ≤ D) :
    ∫⁻ ω, (hit δ c₀ S ω : ℝ≥0∞) ∂(sched n) ≤ (A : ℝ≥0∞) + ε * D := by sorry

end PopRAM
