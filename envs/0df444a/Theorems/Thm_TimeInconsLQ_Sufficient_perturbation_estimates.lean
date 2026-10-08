-- Prove2me | Theorems.Thm_TimeInconsLQ_Sufficient_perturbation_estimates
-- name    : TimeInconsLQ.Sufficient.perturbation_estimates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:26.053187+00:00
-- url     : https://prove2.me/theorems/cd39bbe4-72d0-4805-b5fe-ef9ce27dec31
-- title:
--   Proof of Proposition 3.1, p. 5 — X^{t,ε,v} = X* + Y + Z, E_t[Y_s] = 0, E_t sup|Y|² = O(ε), E_t sup|Z|² = O(ε²)
-- statement:
--   Assume the standing assumptions. Then there is a constant $C\ge0$, depending only on the data, with the following property. Let $u^*$ be an admissible control with state $X^*$, let $t\in[0,T)$, $\varepsilon>0$ and $v\in L^2_{\mathcal F_t}(\Omega;\mathbb R^l)$, let $X^{t,\varepsilon,v}$ be a state of the spike variation $u^{t,\varepsilon,v}_s=u^*_s+v\mathbf 1_{s\in[t,t+\varepsilon)}$, and let $Y$, $Z$ solve
--
--   $$dY_s=A_sY_s\,ds+\sum_{j=1}^d\big[C^j_sY_s+D^j_sv\mathbf 1_{s\in[t,t+\varepsilon)}\big]dW^j_s,\quad Y_t=0;\qquad dZ_s=\big[A_sZ_s+B_s'v\mathbf 1_{s\in[t,t+\varepsilon)}\big]ds+\sum_{j=1}^dC^j_sZ_s\,dW^j_s,\quad Z_t=0,$$
--
--   on $[t,T]$. Then:
--
--   1. $X^{t,\varepsilon,v}_s=X^*_s+Y_s+Z_s$ almost surely, for every $s\in[t,T]$;
--   2. $\mathbb E_t[Y_s]=0$ almost surely, for every $s\in[t,T]$;
--   3. $\mathbb E_t\big[\sup_{s\in[t,T]}|Y_s|^2\big]\le C\,\varepsilon\,|v|^2$ almost surely;
--   4. $\mathbb E_t\big[\sup_{s\in[t,T]}|Z_s|^2\big]\le C\,\varepsilon^2\,|v|^2$ almost surely.
--
--   The paper states the last two as $O(\varepsilon)$ and $O(\varepsilon^2)$; these estimates are what make the remainder in the expansion (3.3) of Proposition 3.1 of order $o(\varepsilon)$.
--
--   **Formalization Note.** The $O(\cdot)$ claims are stated with an explicit constant $C$, uniform in $t$, $\varepsilon$, $v$ and $u^*$ and proportional to $|v|^2$ — a stronger reading than $O(\cdot)$. The conditional bounds 3–4 are stated in the equivalent integrated form $\mathbb E[\mathbf 1_A\sup|Y|^2]\le C\varepsilon\,\mathbb E[\mathbf 1_A|v|^2]$ for every $A\in\mathcal F_t$, which needs no integrability of the supremum. The supremum is taken over the rational times of $[t,T]$ (for a process with continuous paths this is the supremum over $[t,T]$), so the statement holds for every version of $Y$ and $Z$; vectors carry the sup norm, which changes only the constant. $Y,Z$ are solutions of SDEs from time $0$, with initial value $0$ and coefficients multiplied by $\mathbf 1_{s\ge t}$.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 5, proof of Proposition 3.1

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model
import Definitions.Def_TimeInconsLQ_Sufficient_Adjoint

namespace TimeInconsLQ.Sufficient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- Proof of Proposition 3.1, p. 5: the perturbation decomposition and its estimates. Under the
standing assumptions there is a constant `C ≥ 0` (depending only on the data) such that, for
every admissible `u*` with state `X*`, every `t ∈ [0, T)`, `ε > 0`, `v ∈ L²_{𝓕ₜ}(Ω; ℝˡ)`, every
state `Xᵗ'ᵋ'ᵛ` of the spike variation `u^{t,ε,v}` and every solution `Y`, `Z` of the perturbation
equations:
(a) `Xᵗ'ᵋ'ᵛₛ = X*ₛ + Yₛ + Zₛ` a.s., for every `s ∈ [t, T]`;
(b) `E_t[Yₛ] = 0` a.s., for every `s ∈ [t, T]`;
(c) `E_t[sup_{s∈[t,T]} |Yₛ|²] ≤ C ε |v|²` a.s.;
(d) `E_t[sup_{s∈[t,T]} |Zₛ|²] ≤ C ε² |v|²` a.s.
The conditional bounds (c), (d) are stated in the equivalent integrated form over every
`A ∈ 𝓕ₜ`. -/
theorem perturbation_estimates {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ} (M : Data Ω n l d)
    (hM : Standing M) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧
      ∀ (u : ℝ≥0 → Ω → Fin l → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ),
        Admissible M u → IsState M u X →
        ∀ t : ℝ≥0, t < M.T → ∀ ε : ℝ, 0 < ε →
        ∀ v : Ω → Fin l → ℝ, StronglyMeasurable[filt M t] v →
          ∫⁻ ω, ‖v ω‖ₑ ^ 2 ∂M.P < ⊤ →
        ∀ Xε Y Z : ℝ≥0 → Ω → Fin n → ℝ,
          IsState M (spike u t ε v) Xε → IsPertY M t ε v Y → IsPertZ M t ε v Z →
          (∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
              Xε s =ᵐ[M.P] fun ω => X s ω + Y s ω + Z s ω) ∧
          (∀ s : ℝ≥0, t ≤ s → s ≤ M.T → condVec M t (Y s) =ᵐ[M.P] 0) ∧
          (∀ A : Set Ω, MeasurableSet[filt M t] A →
              ∫⁻ ω in A, supSq M.T t Y ω ∂M.P
                ≤ ENNReal.ofReal (Cst * ε) * ∫⁻ ω in A, ‖v ω‖ₑ ^ 2 ∂M.P) ∧
          (∀ A : Set Ω, MeasurableSet[filt M t] A →
              ∫⁻ ω in A, supSq M.T t Z ω ∂M.P
                ≤ ENNReal.ofReal (Cst * ε ^ 2) * ∫⁻ ω in A, ‖v ω‖ₑ ^ 2 ∂M.P) := by sorry

end TimeInconsLQ.Sufficient
