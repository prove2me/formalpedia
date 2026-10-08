-- Prove2me | Theorems.Thm_RegMCBSDE_Simulation_lemma_1
-- name    : RegMCBSDE.Simulation.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:50.925987+00:00
-- url     : https://prove2.me/theorems/ecec6f2f-44b2-4bc8-a839-8a8c53e2829a
-- title:
--   Lemma 1 — contraction of the empirical Picard iterations θ^{i,I,M}_k on the event A^M_k
-- statement:
--   Under the standing assumptions of Section 5 (model satisfying (H1)–(H2), admissible data, orthonormal bases, $M$ independent simulations), let $\alpha^{i,I,M}_k$ be the empirical regression scheme (4) and write
--   $$(\theta^{i,I,M}_k)^*=(\alpha^{i,I,M*}_{0,k},\sqrt h\,\alpha^{i,I,M*}_{1,k},\dots,\sqrt h\,\alpha^{i,I,M*}_{q,k}).$$
--   There are constants $C>0$ and $h_0>0$ such that, for $h<h_0$, every $0\le k\le N-1$ and every outcome of the event $\mathbf A^M_k$ of (27):
--
--   1. (a) for every $i\ge1$, $|\theta^{i+1,I,M}_k-\theta^{i,I,M}_k|^2\le Ch\,|\theta^{i,I,M}_k-\theta^{i-1,I,M}_k|^2$;
--   2. (b) there is a unique vector $\theta^{\infty,I,M}_k$ such that
--   $$\theta^{\infty,I,M}_k=\arg\inf_\theta\frac1M\sum_{m=1}^M\Big(\hat\rho^{N,m}_{0,k+1}(\alpha^{I,I,M}_{0,k+1}\cdot p^m_{0,k+1})+hf^m_k(\alpha^{\infty,I,M}_k)-\theta\cdot v^m_k\Big)^2,$$
--   where $\alpha^{\infty,I,M}_k$ is the coefficient vector whose rescaling is $\theta^{\infty,I,M}_k$;
--   3. (c) $|\theta^{\infty,I,M}_k-\theta^{I,I,M}_k|^2\le[Ch]^I\,|\theta^{\infty,I,M}_k|^2$.
--
--   The lemma shows that on the good event the Picard iterations of the empirical scheme contract at rate $Ch$ towards a fixed point, so that $I$ iterations leave an error of order $h^I$.
--
--   **Formalization Note** At $k=N-1$ the response $\hat\rho^{N,m}_{0,N}(\cdots)$ is read as $\Phi^N(P^{N,m}_{t_N})$, as in the scheme (4). $C$ and $h_0$ depend only on the model; the statement holds for every truncation level $C_0$, every truncation profile $\xi$ and every $I$. Clause (a) is stated for $i\ge1$, where $\theta^{i-1,I,M}_k$ is defined.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 19, Lemma 1 (with the definition of θ, p. 18)

import Mathlib
import Definitions.Def_RegMCBSDE_Simulation_Setting
import Definitions.Def_RegMCBSDE_Simulation_ProjectionScheme
import Definitions.Def_RegMCBSDE_Simulation_EmpiricalScheme

namespace RegMCBSDE.Simulation

open MeasureTheory ProbabilityTheory

/-- Lemma 1, p. 19: contraction of the empirical Picard iterations on the event `𝐀^M_k`.
Write `θ^{i,I,M}_k = (α^{i,I,M}_{0,k}, √h α^{i,I,M}_{1,k}, …, √h α^{i,I,M}_{q,k})`. For `h` small
enough, at every outcome of `𝐀^M_k` (`k ≤ N-1`):
(a) `|θ^{i+1,I,M}_k - θ^{i,I,M}_k|² ≤ C h |θ^{i,I,M}_k - θ^{i-1,I,M}_k|²` for every `i ≥ 1`;
(b) there is a unique vector `θ^{∞,I,M}_k` such that
`θ^{∞,I,M}_k = arg inf_θ (1/M) ∑_m (ρ̂^{N,m}_{0,k+1}(α^{I,I,M}_{0,k+1}·p^m_{0,k+1}) + h f^m_k(α^{∞,I,M}_k) - θ·v^m_k)²`,
where `α^{∞,I,M}_k` is `θ^{∞,I,M}_k` unscaled;
(c) `|θ^{∞,I,M}_k - θ^{I,I,M}_k|² ≤ [C h]^I |θ^{∞,I,M}_k|²`.
At `k = N-1` the response is `Φ^N(P^{N,m}_{t_N})`. `C` and `h₀` depend only on the model. -/
theorem lemma_1 {d q : ℕ} (m : Model d q) (hm : m.Standing) :
    ∃ C > 0, ∃ h₀ > 0, ∀ (d' : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (D : RefData d q d' Ω) (B : Basis q d'),
      m.h D.N < h₀ → D.IsAdmissible m P → B.IsOrthonormal D P →
      ∀ (M : ℕ), 1 ≤ M → ∀ (ΔWs : Fin M → ℕ → Ω → E q) (PNs : Fin M → ℕ → Ω → E d'),
      IsSimulation D P M ΔWs PNs →
      ∀ (ξ : ℝ → ℝ), IsTruncationFn ξ → ∀ (C0 : ℝ) (I : ℕ) (αM : ℕ → (k : ℕ) → Ω → Coeff B k),
      IsEmpiricalScheme m D B C0 ξ ΔWs PNs I αM →
      ∀ k < D.N, ∀ ω ∈ goodEvent m D B ΔWs PNs k,
        (∀ i, 1 ≤ i →
          sqn (theta m D B (αM (i + 1) k ω) - theta m D B (αM i k ω)) ≤
            C * m.h D.N * sqn (theta m D B (αM i k ω) - theta m D B (αM (i - 1) k ω))) ∧
        let IsInf : (Idx B k → ℝ) → Prop := fun θinf =>
          IsMinOn (fun θ : Idx B k → ℝ => (1 / (M : ℝ)) * ∑ s : Fin M,
              (empResp D B C0 ξ PNs (αM I) s k ω
                + m.h D.N * drv m (D.withPath (ΔWs s) (PNs s)) B k (unTheta m D B θinf) ω
                - θ ⬝ᵥ vvec m (D.withPath (ΔWs s) (PNs s)) B k ω) ^ 2)
            Set.univ θinf
        (∃! θinf, IsInf θinf) ∧
        ∀ θinf, IsInf θinf →
          sqn (θinf - theta m D B (αM I k ω)) ≤ (C * m.h D.N) ^ I * sqn θinf := by sorry

end RegMCBSDE.Simulation
