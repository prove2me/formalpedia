-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_corollary_2_8
-- name    : PassiveAdiabaticFT.Thermal.corollary_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:41.829424+00:00
-- url     : https://prove2.me/theorems/1c8db2a8-b580-4215-9d5c-f0744ffa6220
-- title:
--   Corollary 2.8 — linear barrier implies exponentially rare dangerous syndromes
-- statement:
--   Fix constants $c'>0$, $J>0$, $\nu\in\mathbb N$ and an inverse temperature $\beta$ with
--   $$\beta J>\frac{2\ln2}{c'}.\qquad(2.25)$$
--   Then there are constants $a>0$ and $C_0$ such that for every stabilizer code $C$ on $b$ qubits (with any $k\ge1$) whose barrier satisfies $\Delta_b\ge c'Jb$ and in which each qubit belongs to at most $\nu$ checks, there is a Pauli decoder with $R_0=I$ such that for all $\beta'\ge0$
--   $$\frac{Z(\beta)}{Z(\beta')}\,\pi_\beta\Big(\bigcup_\alpha D_\alpha\Big)\le C_0e^{-ab}.\qquad(2.24)$$
--
--   This turns a linear energy barrier into an exponentially small weight of dangerous syndromes at every temperature below a threshold that scales as $1/J$.
--
--   Differences from the source:
--   - encoding: each qubit belongs to O(1) checks; exp(−Ω(n)) → an explicit degree bound ν, and constants a > 0, C₀ chosen after c′, J, ν, β and before the code; reason: the constants of O(1) and Ω(n) are uniform over the family of codes
--   - reading: our syndromes (the decoder of Lemma 2.7) satisfy (2.24) → there is a Pauli decoder with R_0 = I satisfying (2.24) for all β′ ≥ 0; reason: the Lemma 2.7 decoder is itself defined by arbitrary choices; β′ ≥ 0 is the range of (2.18)
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 17, Corollary 2.8 (2.24)–(2.26)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_CodeBlock

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- Corollary 2.8 (p. 17): if `Δ_b ≥ c' J b` and every qubit belongs to at most `ν` checks, then
for every `β` with `βJ > 2 ln 2 / c'` the low-energy decoder gives
`(Z(β)/Z(β')) π_β(⋃_α D_α) ≤ exp(−Ω(b))` (2.24), uniformly over all such codes. -/
theorem corollary_2_8 (c' J β : ℝ) (ν : ℕ) (hc : 0 < c') (hJ : 0 < J)
    (hβ : 2 * Real.log 2 / c' < β * J) :
    ∃ a : ℝ, 0 < a ∧ ∃ C₀ : ℝ, ∀ (b : ℕ) (C : StabCode b),
      c' * J * b ≤ C.barrier J → (∀ q, C.qubitDegree q ≤ ν) →
      ∃ D : PauliDecoder C, ∀ β' : ℝ, 0 ≤ β' →
        C.Z J β / C.Z J β' * C.gibbsSet J β D.Bdec ≤ C₀ * Real.exp (-(a * b)) := by sorry

end PassiveAdiabaticFT.Thermal
