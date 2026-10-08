-- Prove2me | Theorems.Thm_RegMCBSDE_Simulation_theorem_3
-- name    : RegMCBSDE.Simulation.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:50.526015+00:00
-- url     : https://prove2.me/theorems/94b1b133-a890-481a-86e2-f458b21294f9
-- title:
--   Theorem 3 — simulation error of the empirical regression scheme in the number M of paths
-- statement:
--   Let the model satisfy (H1)–(H2), let $\xi$ be a truncation profile, let $I\ge3$, let each function basis $p_{l,k}$ be orthonormal with $\mathbb E|p_{l,k}|^4<\infty$, and let $C_0\ge0$ be a constant for which the a priori bounds of Proposition 2 hold, with $\rho^N_{l,k}=\max(1,C_0|p_{l,k}|)$. Let $Y^{N,I,I},Z^{N,I,I}$ be the projection–Picard scheme of Definition 1 and $Y^{N,I,I,M},Z^{N,I,I,M}$ the empirical regression scheme (4) computed from $M\ge1$ independent simulations. For $h$ small enough, for any $0\le k\le N-1$,
--   $$\begin{aligned}
--   &\mathbb E|Y^{N,I,I}_{t_k}-Y^{N,I,I,M}_{t_k}|^2+h\sum_{j=k}^{N-1}\mathbb E|Z^{N,I,I}_{t_j}-Z^{N,I,I,M}_{t_j}|^2\\
--   &\le 9\sum_{j=k}^{N-1}\mathbb E\big(|\rho^N_j(P^N_{t_j})|^2\mathbf 1_{[\mathbf A^M_k]^c}\big)+Ch^{I-1}\sum_{j=k}^{N-1}\big[1+|S_0|^2+\mathbb E|\rho^N_j(P^N_{t_j})|^2\big]\\
--   &\quad+\frac{C}{hM}\sum_{j=k}^{N-1}\Big(\mathbb E\|v_jv_j^*-\mathrm{Id}\|_F^2\,\mathbb E|\rho^N_j(P^N_{t_j})|^2+T_j\\
--   &\qquad+h^2\,\mathbb E\Big[|v_j|^2\Big(1+|S^N_{t_j}|^2+|p_{0,j}|^2\,\mathbb E|\rho^N_{0,j}(P^N_{t_j})|^2+\frac1h\sum_{l=1}^q|p_{l,j}|^2\,\mathbb E|\rho^N_{l,j}(P^N_{t_j})|^2\Big)\Big]\Big),
--   \end{aligned}$$
--   where $T_j=\mathbb E(|v_j|^2|p_{0,j+1}|^2)\,\mathbb E|\rho^N_{0,j+1}(P^N_{t_{j+1}})|^2$ for $j\le N-2$ and $T_{N-1}=\mathbb E(|v_{N-1}|^2|\Phi^N(P^N_{t_N})|^2)$. The constant $C$ and the threshold on $h$ depend only on the model and on $\xi$.
--
--   The theorem is the paper's main result on the number of simulated paths: it bounds the simulation error nonasymptotically by a term that vanishes as $\mathbb P(\mathbf A^M_k)\to1$, a term of order $h^{I-1}$ from the finite number of Picard iterations, and terms of order $1/(hM)$ governed by the variance of the regression quantities.
--
--   **Formalization Note** Two corrections of the printed statement, both taken from the paper's own proof (Step 5, term $B_2$, p. 21, and (33)): (1) the printed $j=N-1$ summand contains $p_{0,N}$, which is not defined (the bases exist for $k\le N-1$ and the scheme regresses $\Phi^N(P^{N,m}_{t_N})$ at the last step), so it is replaced by $\mathbb E(|v_{N-1}|^2|\Phi^N(P^N_{t_N})|^2)$; (2) the printed factor $\mathbb E|\rho^N_{0,j}(P^N_{t_j})|^2$ next to $\mathbb E(|v_j|^2|p_{0,j+1}|^2)$ is replaced by $\mathbb E|\rho^N_{0,j+1}(P^N_{t_{j+1}})|^2$, which is the bound the proof obtains on the response coefficient $|\alpha^{I,I}_{0,j+1}|^2$. All expectations are taken in $[0,\infty]$. The paper's "$C_0$ large enough" is formalized as the hypothesis that the bounds of Proposition 2 hold for $C_0$; independence of the reference path from the simulations is assumed explicitly. (H3) is dropped (it concerns the continuous-time terminal condition).
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, pp. 16–17, Theorem 3

import Mathlib
import Definitions.Def_RegMCBSDE_Simulation_Setting
import Definitions.Def_RegMCBSDE_Simulation_ProjectionScheme
import Definitions.Def_RegMCBSDE_Simulation_EmpiricalScheme

namespace RegMCBSDE.Simulation

open MeasureTheory ProbabilityTheory

/-- Theorem 3, pp. 16–17: the simulation error of the empirical regression scheme.
Assume (H1)–(H2), `I ≥ 3`, orthonormal bases with `𝔼|p_{l,k}|⁴ < ∞`, `M ≥ 1` independent
simulations (independent of the reference path), a constant `C₀ ≥ 0` for which the bounds of
Proposition 2 hold, and let `ρ^N_{l,k} = max(1, C₀|p_{l,k}|)`. For `h` small enough, for any
`0 ≤ k ≤ N-1`,
`𝔼|Y^{N,I,I}_{t_k} - Y^{N,I,I,M}_{t_k}|² + h ∑_{j=k}^{N-1} 𝔼|Z^{N,I,I}_{t_j} - Z^{N,I,I,M}_{t_j}|²`
`≤ 9 ∑_{j=k}^{N-1} 𝔼(|ρ^N_j(P^N_{t_j})|² 𝟏_{[𝐀^M_k]^c}) + C h^{I-1} ∑_{j=k}^{N-1} [1 + |S₀|² + 𝔼|ρ^N_j(P^N_{t_j})|²]`
`+ C/(hM) ∑_{j=k}^{N-1} ( 𝔼‖v_j v_j^* - Id‖²_F 𝔼|ρ^N_j(P^N_{t_j})|² + T_j`
`+ h² 𝔼[|v_j|² (1 + |S^N_{t_j}|² + |p_{0,j}|² 𝔼|ρ^N_{0,j}(P^N_{t_j})|² + (1/h) ∑_{l=1}^q |p_{l,j}|² 𝔼|ρ^N_{l,j}(P^N_{t_j})|²)] )`,
with `T_j = 𝔼(|v_j|² |p_{0,j+1}|²) 𝔼|ρ^N_{0,j+1}(P^N_{t_{j+1}})|²` for `j ≤ N-2` and
`T_{N-1} = 𝔼(|v_{N-1}|² |Φ^N(P^N_{t_N})|²)`.

Corrections of the printed statement (both follow the paper's proof, Step 5, term `B₂`, p. 21,
and (33)): (1) the printed `j = N-1` summand contains `p_{0,N}`, which is undefined; the response
at `j = N-1` is `Φ^N(P^N_{t_N})`, so `T_{N-1}` is stated as above; (2) the printed factor
`𝔼|ρ^N_{0,j}(P^N_{t_j})|²` in the second summand is replaced by `𝔼|ρ^N_{0,j+1}(P^N_{t_{j+1}})|²`,
the bound on the response coefficient `|α^{I,I}_{0,j+1}|²`. `C` and `h₀` depend only on the model
and on `ξ`; never on `N`, `I`, `M`, `k`, `C₀`, the bases, `S₀`, `d'` or the probability space. -/
theorem theorem_3 {d q : ℕ} (m : Model d q) (hm : m.Standing) (ξ : ℝ → ℝ) (hξ : IsTruncationFn ξ) :
    ∃ C > 0, ∃ h₀ > 0, ∀ (d' : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (D : RefData d q d' Ω) (B : Basis q d'),
      m.h D.N < h₀ → D.IsAdmissible m P → B.IsOrthonormal D P → B.HasFourthMoments D P →
      ∀ (I : ℕ), 3 ≤ I → ∀ (M : ℕ), 1 ≤ M →
      ∀ (ΔWs : Fin M → ℕ → Ω → E q) (PNs : Fin M → ℕ → Ω → E d'), IsSimulation D P M ΔWs PNs →
      ∀ (C0 : ℝ), 0 ≤ C0 →
      ∀ (α : ℕ → (k : ℕ) → Coeff B k), IsProjectionScheme m D B P I α → Prop2Bounds m D B P C0 α →
      ∀ (αM : ℕ → (k : ℕ) → Ω → Coeff B k), IsEmpiricalScheme m D B C0 ξ ΔWs PNs I αM →
      ∀ k < D.N,
        let h := m.h D.N
        let S := m.euler D.N D.S0 D.ΔW
        let v := vvec m D B
        let Eρ : ℕ → ENNReal := fun j => ∫⁻ ω, ENNReal.ofReal (rhoSq B C0 j (D.PN j ω)) ∂P
        let Eρl : Fin (q + 1) → ℕ → ENNReal := fun l j =>
          ∫⁻ ω, ENNReal.ofReal (rho B C0 l j (D.PN j ω) ^ 2) ∂P
        let Tj : ℕ → ENNReal := fun j =>
          if j + 1 < D.N then
            (∫⁻ ω, ENNReal.ofReal (sqn (v j ω) * sqn (B.p 0 (j + 1) (D.PN (j + 1) ω))) ∂P) * Eρl 0 (j + 1)
          else ∫⁻ ω, ENNReal.ofReal (sqn (v j ω) * D.ΦN (D.PN D.N ω) ^ 2) ∂P
        (∫⁻ ω, ENNReal.ofReal
            ((α I k 0 ⬝ᵥ B.p 0 k (D.PN k ω) - empY D B C0 ξ k (αM I k) ω) ^ 2) ∂P)
          + ENNReal.ofReal h * ∑ j ∈ Finset.Ico k D.N, ∫⁻ ω, ENNReal.ofReal
            (∑ l : Fin q, (α I j l.succ ⬝ᵥ B.p l.succ j (D.PN j ω) - empZ m D B C0 ξ j (αM I j) l ω) ^ 2) ∂P
        ≤ 9 * ∑ j ∈ Finset.Ico k D.N,
              ∫⁻ ω in (goodEvent m D B ΔWs PNs k)ᶜ, ENNReal.ofReal (rhoSq B C0 j (D.PN j ω)) ∂P
          + ENNReal.ofReal (C * h ^ (I - 1)) *
              ∑ j ∈ Finset.Ico k D.N, (1 + ENNReal.ofReal (‖D.S0‖ ^ 2) + Eρ j)
          + ENNReal.ofReal (C / (h * M)) * ∑ j ∈ Finset.Ico k D.N,
              ((∫⁻ ω, ENNReal.ofReal (frobSq (Matrix.vecMulVec (v j ω) (v j ω) - 1)) ∂P) * Eρ j
                + Tj j
                + ENNReal.ofReal (h ^ 2) * ∫⁻ ω, ENNReal.ofReal (sqn (v j ω)) *
                    (1 + ENNReal.ofReal (‖S j ω‖ ^ 2)
                      + ENNReal.ofReal (sqn (B.p 0 j (D.PN j ω))) * Eρl 0 j
                      + ENNReal.ofReal (1 / h) * ∑ l : Fin q,
                          ENNReal.ofReal (sqn (B.p l.succ j (D.PN j ω))) * Eρl l.succ j) ∂P) := by sorry

end RegMCBSDE.Simulation
