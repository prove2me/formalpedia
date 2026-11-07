-- Prove2me | Theorems.Thm_QPSpinParisi_theorem_1
-- name    : QPSpinParisi.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:25.504202+00:00
-- url     : https://prove2.me/theorems/361c2686-2103-49d9-b439-aefa0a403a06
-- title:
--   Theorem 1 — $E^\star_{n,\mathrm{prod}}$ concentrates, $\lim\mathbb E E^\star_{n,\mathrm{prod}}=\inf_{\mathcal U}P_\xi$, and $P_\xi$ is strictly convex
-- statement:
--   Let $(c_p)_{p\ge2}$ be real with $\sum_p2^pc_p^2<\infty$ and some $c_p\ne0$, and let $H_n$ be the quantum mixed $p$-spin Hamiltonian with i.i.d. standard Gaussian coefficients. For $E^\star_{n,\mathrm{prod}}=n^{-1/2}\max_{|\phi\rangle\in S^n_{\mathrm{prod}}}\langle\phi|H_n|\phi\rangle$:
--
--   1. $E^\star_{n,\mathrm{prod}}-\mathbb E(E^\star_{n,\mathrm{prod}})\xrightarrow{P}0$.
--   2. The limit
--   $$E^\star_{\mathrm{prod}}=\lim_{n\to\infty}\mathbb E(E^\star_{n,\mathrm{prod}})=\inf_{\gamma\in\mathcal U}P_\xi(\gamma)$$
--   exists and equals the infimum of the Parisi functional, and the infimum is attained.
--   3. $P_\xi$ is strictly convex, hence has a unique minimizer $\gamma^\star\in\mathcal U$.
--
--   This is the Parisi formula for the maximal energy over product states of any mixed quantum $p$-spin Hamiltonian, infinite mixtures and odd $p$ included.
--
--   Differences from the source:
--   - reading: $\sum_{p\ge2}$ in (2.1) → the sum over $p$ stops at $p=n$; reason: a $p$-local string needs $p$ distinct sites, and (3.1), (3.5) print $\sum_{p=2}^n$
--   - reading: "strictly convex, hence has a unique minimizer" → existence of a minimizer is stated; reason: p.4: "there exists a unique $\gamma^\star\in\mathcal U$ such that $E^\star_{\mathrm{prod}}=P_\xi(\gamma^\star)$"
--   - reading: "the Brownian filtration" → the completed natural filtration of all three coordinates; reason: the usual meaning; the supremum in (2.3) does not change
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - generalization: no integrability statement → the clause `Integrable (En c n)` is added; reason: otherwise $\int E^\star_{n,\mathrm{prod}}$ could be a default value; the source's claim follows by dropping it
--   - encoding: increasing tuples $\bar i$ and strings $\bar a$ → subsets $S$ with $|S|\ge2$ and maps $S\to$ `Fin 3`; reason: the same index set
--   - encoding: $\int_s^1\sqrt{\zeta}\,dB$ → the increment of the process `noise` between $s$ and $1$; reason: the Wiener integral, tied to $B$ by `HasBrownianItoIntegral`
--   - encoding: $\xi$, $\zeta=\xi''$ → the explicit power series; reason: under the hypothesis these are the derivatives on $[-1,1]$
--   - encoding: the complex number $\langle\phi|H_n|\phi\rangle$ → its real part; reason: $H_n$ is Hermitian, so the value is real
--   - encoding: $\xrightarrow{P}$ on a common space → the measure of the deviation event, for each $n$ on its own space; reason: no common space exists across $n$, and convergence in probability only reads these numbers
--   - encoding: functions on $[0,1)$ → `Ico 0 1 → ℝ`, extended by $0$ under integrals; reason: integrals over $[0,1]$ do not see the point $1$
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Theorem 1, p.4 (PDF p.4)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_En
import Definitions.Def_QPSpinParisi_gaussMeas
import Definitions.Def_QPSpinParisi_Pf
import Definitions.Def_QPSpinParisi_USet

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Theorem 1, p.4, PDF p.4: `E⋆_{n,prod} - E(E⋆_{n,prod}) → 0` in probability; further `E⋆_prod := lim_{n→∞} E(E⋆_{n,prod}) = inf_{γ ∈ U} P_ξ(γ)`; and `P_ξ` is
strictly convex, hence has a unique minimizer.

**Formalization Note** `IsLeast` carries the infimum and its attainment by `γs`, the "unique `γ⋆ ∈ U` such that `E⋆_prod = P_ξ(γ⋆)`" of p.4. The clause `Integrable (En c n)` makes `∫ En`
an honest expectation. The spaces change with `n`, so convergence in probability is written with the measure of the deviation event. The statement holds for every noise `W`, and `exists_noise`
says one exists. -/
theorem theorem_1 (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) :
    (∀ n, Integrable (En c n) (gaussMeas n)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => gaussMeas n {α | ε ≤ |En c n α - ∫ a, En c n a ∂(gaussMeas n)|}) atTop (𝓝 0)) ∧
    (∃ γs ∈ USet, Tendsto (fun n => ∫ a, En c n a ∂(gaussMeas n)) atTop (𝓝 (Pf W γs)) ∧
      IsLeast (Pf W '' USet) (Pf W γs) ∧ ∀ γ ∈ USet, Pf W γ = Pf W γs → γ = γs) ∧
    StrictConvexOn ℝ USet (Pf W) := by sorry

end QPSpinParisi
