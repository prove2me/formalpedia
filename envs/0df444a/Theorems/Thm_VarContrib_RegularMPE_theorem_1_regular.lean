-- Prove2me | Theorems.Thm_VarContrib_RegularMPE_theorem_1_regular
-- name    : VarContrib.RegularMPE.theorem_1_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:35.865978+00:00
-- url     : https://prove2.me/theorems/24ce1ef5-278c-419f-8256-ca315e9a9054
-- title:
--   Theorem 1, pp. 14–15, regular instance — conditions (i)–(iv) make the regular rate u*_i the best response within Σ_i, with payoff U
-- statement:
--   Theorem 1 of the paper gives sufficient conditions for a best response within the class $\Sigma_i$. This is its instance in which the opponent $j$ contributes at a regular feedback rate $d\xi_{jt}=u_j(Z_t)dt$ and the candidate at a regular feedback rate $d\xi^*_{it}=u^*_i(Z_t)dt$, so that $D_j=D_i=\emptyset$ and $C_j=C_i=I$.
--
--   Assume the standing assumptions and Assumptions 1–3. Let $u_j,u^*_i\in\mathcal U$ be nonnegative on $I$, and let $U\in C^2(I)$ be nondecreasing and bounded above on $I$ with
--
--   1. (iii) $\max\{\mathcal AU(x)+\pi(x)+u_j(x)U'(x)+vU'(x)-vk,\ U'(x)-k\}\le0$ for all $x\in I$ and $v\ge0$;
--   2. (iv) $\mathcal AU(x)+\pi(x)+u_j(x)U'(x)+u^*_i(x)U'(x)-u^*_i(x)k=0$ for all $x\in I$.
--
--   Then for every $x\in I$ and every solution $Z$ of $dZ_t=[\mu+u^*_i+u_j](Z_t)dt+\sigma(Z_t)dW_t$, $Z_0=x$:
--
--   1. $e^{-rt}(\pi(Z_t)-k\,u^*_i(Z_t))$ is $P\otimes dt$-integrable, and
--   $$\mathbb E\int_0^\infty e^{-rt}\big(\pi(Z_t)-k\,u^*_i(Z_t)\big)dt=U(x);$$
--   2. for every admissible control $\zeta\in\Sigma_i$ and solution $Z'$ of $dZ'_t=[\mu+u_j](Z'_t)dt+\sigma(Z'_t)dW_t+d\zeta_t$, $Z'_{0-}=x$, the payoff of $\zeta$ is at most $U(x)$.
--
--   The full printed statement: *Suppose Assumptions 1–3 hold. Assume player j's Markov strategy $\xi_j\in\mathcal M_j\cap\Sigma_j$ that satisfies $d\xi_{jt}=u_j(Z_t)dt+d\xi^l_{jt}+\Delta\xi_{jt}$ for some function $u_j(\cdot)\ge0$. Suppose that there exist a function $U(\cdot)$ on $I$ and some Markov strategy $\xi^*_i\in\mathcal M_i\cap\Sigma_i$ that satisfy the SDE $d\xi^*_{it}=u^*_i(Z_t)dt+d\xi^{*l}_{it}+\Delta\xi^*_{it}$ (5) for some $u^*_i(\cdot)\ge0$ and conditions (i) $U\in C^2(C_j)\cap C(I)$, non-decreasing and bounded from above, $U'=0$ in the interior of $D_j$ and $U'(Z_t)d\xi^l_{jt}=0$; (ii) an extension $\tilde U\in C^2(I)$ equal to $U$ on $C_j$ with $\tilde U'$ bounded on $D_j$; (iii) as above on $C_j$; (iv) with $D_i=\{x\in I:\Delta\xi^*_{it}>0 \text{ whenever } x=Z_{t-}\}\cap C_j$ and $C_i=\{x\in I:\Delta\xi^*_{it}=0\text{ whenever }x=Z_{t-}\}\cap C_j$, the equation of (iv) on $C_i$ and $U'=k_i$ on $D_i$. Then $\xi^*_i$ is the best response to $\xi_j$ amongst all control processes that belong to $\Sigma_i$, i.e., $V_i(x;\xi^*_i,\xi_j)=\sup_{\xi_i\in\Sigma_i}V_i(x;\xi_i,\xi_j)$.*
--
--   This is the step of Theorem 2's proof that identifies each player's payoff with $V$.
--
--   **Formalization Note.** With $\xi_j$ and $\xi^*_i$ regular, $D_j=D_i=\emptyset$, so the clauses about $D_j$, $\xi^l_j$, $\tilde U$ and $D_i$ are vacuous and are omitted. "$=\sup_{\Sigma_i}$" is posed as "$=U(x)$, and $U(x)\ge$ every $\Sigma_i$ payoff", the proof's own conclusion (p. 37). The symmetric game has one $\pi$ and one $k$.
-- source:
--   Kwon, Game of Variable Contributions to the Common Good under Uncertainty, arXiv:1904.00500v1, pp. 14–15, Theorem 1 (instance D_j = D_i = ∅ used in the proof of Theorem 2, pp. 37–38)

import Mathlib
import Definitions.Def_VarContrib_RegularMPE_Model
import Definitions.Def_VarContrib_RegularMPE_Setting
import Definitions.Def_VarContrib_RegularMPE_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VarContrib.RegularMPE

/-- Theorem 1 (Kwon, pp. 14–15), in the instance used by the proof of Theorem 2: the opponent
`j` contributes at a regular feedback rate `u_j ≥ 0` and the candidate `ξ*_i` at a regular
feedback rate `u*_i ≥ 0` (so `D_j = D_i = ∅`, `C_j = C_i = I`). If `U ∈ C²(I)` is
nondecreasing and bounded above and satisfies (iii) and (iv), then along every state `Z` of the
profile `(ξ*_i, ξ_j)` player `i`'s payoff is `U(x)`, and every admissible `Σ_i` deviation pays
at most `U(x)`. -/
theorem theorem_1_regular {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (hst : Standing m S) (uj ui : ℝ → ℝ) (huj : InU m uj) (huj0 : ∀ y ∈ m.I, 0 ≤ uj y)
    (hui : InU m ui) (hui0 : ∀ y ∈ m.I, 0 ≤ ui y) (U : ℝ → ℝ)
    (hU : ContDiffOn ℝ 2 U m.I) (hUmono : MonotoneOn U m.I) (hUbdd : BddAbove (U '' m.I))
    (hiii : ∀ x ∈ m.I, ∀ v : ℝ, 0 ≤ v →
      max (gen m U x + m.π x + uj x * deriv U x + v * deriv U x - v * m.k)
        (deriv U x - m.k) ≤ 0)
    (hiv : ∀ x ∈ m.I,
      gen m U x + m.π x + uj x * deriv U x + ui x * deriv U x - ui x * m.k = 0) :
    ∀ x ∈ m.I, ∀ Z : ℝ≥0 → Ω → ℝ,
      IsStateSol m S (fun y => m.μ y + ui y + uj y) x (fun _ _ => 0) Z →
        Integrable (fun p : Ω × ℝ => Real.exp (-(m.r * p.2)) *
            (m.π (Z p.2.toNNReal p.1) - m.k * ui (Z p.2.toNNReal p.1)))
          (S.P.prod (volume.restrict (Ioi (0 : ℝ)))) ∧
        regPay m S ui Z = U x ∧
        ∀ ζ Z' : ℝ≥0 → Ω → ℝ, IsStateSol m S (fun y => m.μ y + uj y) x ζ Z' →
          Adm m S ζ Z' → InSigma m S ζ Z' → devPay m S ζ Z' ≤ U x := by sorry

end VarContrib.RegularMPE
