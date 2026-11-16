-- Prove2me | Theorems.Thm_QPSpinProfile_Supplement_theorem_4_16
-- name    : QPSpinProfile.Supplement.theorem_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:33:12.991204+00:00
-- url     : https://prove2.me/theorems/c5456128-58db-4680-9a21-1d2139c5491c
-- title:
--   Theorem 4.16 — reverse magic with arbitrary clean ancillas has an $\Omega(\sqrt n)$ ground-state gap
-- statement:
--   Let $H_{n,p} = \binom np^{-1/2}\sum_{P\in\mathcal P_{n,p}} g_P\,P$ be the dense quantum $p$-spin Hamiltonian on $n$ qubits with independent standard Gaussian couplings $g_P$, let $\lambda_{\max}(H_{n,p})$ be its largest eigenvalue, and for a class $\mathcal C_n$ of $n$-qubit states let
--   $$
--   \Delta^{\mathrm{opt}}_{n,p}(\mathcal C_n) = \lambda_{\max}(H_{n,p}) - \sup_{\rho\in\mathcal C_n}\operatorname{Tr}(H_{n,p}\rho)
--   $$
--   be the ground-state gap of the class. Let $\mathsf{revmag}^{[D],\mathrm{clean}}_n$ be the clean-ancilla reverse-magic class: pure states $|\psi\rangle$ with $CQ|0^{n+r}\rangle = |\psi\rangle|0^r\rangle$ for some $r\ge 0$, Clifford $C$ and depth-$D$ circuit $Q$ of one- and two-qubit gates.
--
--   **Theorem 4.16 (Reverse magic with arbitrary clean ancillas).** Fix an integer $D \ge 1$. There exists $p_0 = p_0(D) < \infty$ such that, for every fixed $p \ge p_0$, there is $c_{p,D} > 0$ for which
--   $$
--   \mathbb P\Bigl(\Delta^{\mathrm{opt}}_{n,p}\bigl(\mathsf{revmag}^{[D],\mathrm{clean}}_n\bigr) \ge c_{p,D}\sqrt n\Bigr) \longrightarrow 1 \qquad (n\to\infty).
--   $$
--   The conclusion is uniform over the number of clean ancillas.
--
--   One round of a constant-depth circuit followed by an arbitrary Clifford, with any number of ancillas that are returned to $|0\rangle$, therefore stays a constant multiple of $\sqrt n$ below the ground-state energy of the dense quantum $p$-spin glass with high probability, once $p$ is large enough in terms of $D$. In contrast with the linear-width results of the paper's §4.2, the number of ancillas is unbounded.
--
--   **Formalization Note** $\Delta^{\mathrm{opt}}$, the Hamiltonian and the disorder law are the published definitions of the base mission (`deltaOpt`, `hamiltonian`, `gaussMeasure`). $p_0$ depends only on $D$ and $c$ only on $(p,D)$. The uniformity over the number of ancillas is carried by the class itself, which is the union over every $r\ge 0$; neither $p_0$ nor $c$ depends on $r$.
--
--   Differences from the source:
--
--   - encoding: class of pure states $|\psi\rangle$ → set of density matrices $|\psi\rangle\langle\psi|$ with $\psi$ a unit vector; reason: the base mission's classes are sets of density matrices; same states
--   - encoding: $\mathsf{cliff}_{n+r}$ as a quotient by $U(1)$ → a unitary representative with the normalizer property; reason: the paper prescribes choosing any representative when a Clifford acts on a state (p.45); a phase change only multiplies $\psi$ by a phase and leaves $|\psi\rangle\langle\psi|$ unchanged
--   - encoding: "depth-$D$ matching circuit" → $\mathrm{Circ}[D]_{n+r}$, depth at most $D$; reason: the paper's own reading (Proposition 4.14, Lemma 4.15); identity layers make depth exactly $D$ the same class
--   - encoding: probability tending to $1$ → `Tendsto` of the `gaussMeasure n p`-measure of the event $\{c\sqrt n \le \Delta^{\mathrm{opt}}\}$ along $n\to\infty$; reason: Lean convention; same statement
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Theorem 4.16, p.66 (PDF p.69); Definition 4.11, p.59 (PDF p.62)

import Mathlib
import Definitions.Def_QPSpinProfile_maxEnergy
import Definitions.Def_QPSpinProfile_Supplement_revmagClean

namespace QPSpinProfile.Supplement

open MeasureTheory Filter Topology

/-- **Theorem 4.16 (Reverse magic with arbitrary clean ancillas)** (Al-Ghattas, Gamarnik, Kiani,
*Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held
version, sha256 a0a1ec89…), p.66, PDF p.69). Fix an integer `D ≥ 1`. There exists
`p₀ = p₀(D) < ∞` such that, for every fixed `p ≥ p₀`, there is `c_{p,D} > 0` for which
`P(Δ^opt_{n,p}(revmag^{[D],clean}_n) ≥ c_{p,D}√n) → 1`. The conclusion is uniform over the number of
clean ancillas.

**Formalization Note** `Δ^opt_{n,p}` is the base mission's `deltaOpt` (`λ_max(H_{n,p})` minus the
supremum of `Tr(H_{n,p}ρ)` over the class), and the probability is under the base mission's
disorder law `gaussMeasure n p`. `p₀` depends only on `D`, and `c` only on `p` and `D`. Uniformity
over the number of clean ancillas is carried by the class: `revmagClean D n` takes the union over
every `r ≥ 0`, so neither `p₀` nor `c` depends on `r`. -/
theorem theorem_4_16 :
    ∀ D : ℕ, 1 ≤ D → ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => gaussMeasure n p
        {g | c * Real.sqrt n ≤ deltaOpt n p (revmagClean D n) g}) atTop (𝓝 1) := by sorry

end QPSpinProfile.Supplement
