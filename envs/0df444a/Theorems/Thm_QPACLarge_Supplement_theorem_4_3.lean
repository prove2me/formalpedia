-- Prove2me | Theorems.Thm_QPACLarge_Supplement_theorem_4_3
-- name    : QPACLarge.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:26:41.015691+00:00
-- url     : https://prove2.me/theorems/da8f7014-a2ce-4f03-8047-7a336f587f3a
-- title:
--   Theorem 4.3 — under subexponential OWFs, no $o(2^{m/2})$-time classical learner reaches correlation $\rho2^{-m/2}$ on $\mathrm{SIZE}[m^K]$ with probability $p>1/2$
-- statement:
--   Assume that subexponentially secure one-way functions exist. Then there is a fixed integer $K \ge 1$ such that for every real $\rho > 0$ and every $p > 1/2$ there is no uniform randomized classical algorithm $A$ with the following property: there is a time bound $T(m) = o(2^{m/2})$ such that, for every sufficiently large input length $m$ and every target $f \in \mathrm{SIZE}[m^K]$ on $m$ bits, $A$ runs in time $T(m)$ with membership queries to $f$ and outputs a deterministic Boolean circuit $h$ satisfying
--   $$
--   \Pr_A\big[\mathrm{corr}(H, F) \ge \rho\, 2^{-m/2}\big] \ge p,
--   $$
--   where $F(x) = (-1)^{f(x)}$, $H(x) = (-1)^{h(x)}$ and $\mathrm{corr}(H,F) = \mathbb E_{x\sim U_m}[H(x)F(x)] = 2\Pr_{x\sim U_m}[h(x)=f(x)] - 1$.
--
--   $\mathrm{SIZE}[s]$ is the set of Boolean functions computed by circuits with at most $s$ gates. With $\rho = 2a_0$ this is Theorem 1.4 Item (ii): under a generic cryptographic assumption, no classical learner running in time $o(2^{m/2})$ matches the guarantee of the one-example quantum learner of Theorem 3.3 on a fixed polynomial-size circuit class.
--
--   **Formalization Note** The OWF hypothesis is the published `SubexpOWFExists`, $\mathrm{SIZE}[m^K]$ the published `InSIZE`. A uniform randomized algorithm is one oracle Turing machine for all $m$, and its success probability with time bound $T(m)$ is the supplement's `omqSuccess`, in which runs exceeding $T(m)$ steps fail. $T(m) = o(2^{m/2})$ is $T(m)/2^{m/2} \to 0$. The correlation is written as $2\,\mathrm{agreement}(f,h) - 1$ (Eq. (2)).
--
--   Differences from the source:
--   - encoding: a uniform randomized classical algorithm that runs in $o(2^{m/2})$ time with membership queries → one `HMBinPacking.OracleMachine` $A$ and one $T : \mathbb N \to \mathbb N$ with $T(m)/2^{m/2} \to 0$; success counts the coin strings in $\{0,1\}^{2^m}$ on which $A$ halts within $T(m)$ steps with a circuit code (binary `encBoolCircuitBin`) on its output stack satisfying the event; reason: the model of Section 2.2 and the truncation in the proof (p.32: "Truncate it after its promised running time"), so a run that does not finish in time fails; the coin length $2^m$ does not depend on $T$ (no advice) and exceeds the $O(T(m))$ coins a run can read
--   - reading: "for every … $f \in \mathrm{SIZE}[m^K]$ … it runs in $o(2^{m/2})$ time" → one time bound $T(m) = o(2^{m/2})$, uniform over the targets of length $m$; reason: the proof uses one query bound $q_m = o(2^{m/2})$ for all targets (p.33); a time bound depending on $f$ is not a running time of the algorithm
--   - encoding: $\mathrm{corr}(H,F) \ge \rho\,2^{-m/2}$ → $\rho\,2^{-m/2} \le 2\,\mathrm{agreement}(f,h) - 1$; reason: Eq. (2), p.14: an identity
--   - encoding: subexponentially secure one-way functions (p.19) → the published `SubexpOWFExists`; reason: the base mission's encoding: clocked inverters with $\lfloor 2^{n^\varepsilon}\rfloor$ steps and coins; clocking is absorbed by the existential $\varepsilon$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 4.3, p.32 (and Theorem 1.4 Item (ii), p.6; proof pp.32–33)

import Mathlib
import Definitions.Def_QPACLarge_Supplement_omqSuccess
import Definitions.Def_QPACLarge_agreement
import Definitions.Def_QPACLarge_InSIZE
import Definitions.Def_QPACLarge_SubexpOWFExists

namespace QPACLarge.Supplement

open QAlgorithms QPACLarge Filter

/-- **Theorem 4.3 (Conditional Classical Hardness for Polynomial Size Concepts)**, together with
**Theorem 1.4 Item (ii)**.
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*,
arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 4.3, p.32: "Assume the existence of
subexponentially secure one-way functions. There is a fixed integer `K ≥ 1` such that, for every
`ρ > 0` and `p > 1/2`, no uniform randomized classical algorithm `A` has the following property:
for every sufficiently large input length `m` and every target `f ∈ SIZE[m^K]` on `m` bits, it runs
in `o(2^{m/2})` time with membership queries and outputs a deterministic Boolean circuit `h`
satisfying `Pr_A[corr(H, F) ≥ ρ 2^{−m/2}] ≥ p`, where `F(x) = (−1)^{f(x)}` and
`H(x) = (−1)^{h(x)}`." Theorem 1.4 Item (ii), p.6, is the case `ρ = 2a₀` (by Eq. (2), p.14).

**Formalization Note.** The OWF hypothesis is the published `SubexpOWFExists`; `SIZE[m^K]` is the
published `InSIZE f (m ^ K)`. A uniform randomized algorithm is one oracle machine for all `m`; it
"runs in `o(2^{m/2})` time" when there is one time bound `T(m)` with `T(m)/2^{m/2} → 0`, and its
success at length `m` is `omqSuccess A (T m) m f ·` (runs exceeding `T(m)` steps fail).
`corr(H, F) = E_x[H(x)F(x)]` is written `2·agreement(f, h) − 1` (Eq. (2), p.14). -/
theorem theorem_4_3 (hOWF : SubexpOWFExists) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ ρ : ℝ, 0 < ρ → ∀ p : ℝ, 1 / 2 < p →
      ¬ ∃ (A : HMBinPacking.OracleMachine) (T : ℕ → ℕ),
        Tendsto (fun m : ℕ => (T m : ℝ) / (2 : ℝ) ^ ((m : ℝ) / 2)) atTop (nhds 0) ∧
        ∀ᶠ m : ℕ in atTop, ∀ f : Qubits m → Bool, InSIZE f (m ^ K) →
          p ≤ omqSuccess A (T m) m f (fun h =>
            ρ * (2 : ℝ) ^ (-(m : ℝ) / 2) ≤ 2 * agreement f (fun x => h.eval x 0) - 1) := by sorry

end QPACLarge.Supplement
