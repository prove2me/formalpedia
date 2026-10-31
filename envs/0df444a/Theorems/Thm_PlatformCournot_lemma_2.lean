-- Prove2me | Theorems.Thm_PlatformCournot_lemma_2
-- name    : PlatformCournot.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:55.100885+00:00
-- url     : https://prove2.me/theorems/bdce7fad-3c7c-41cc-a465-4acc946b4e57
-- title:
--   Lemma 2 — linearizing costs at equilibrium by their right derivative does not decrease the price of anarchy
-- statement:
--   Let $C=(C_1,\dots,C_n)$ satisfy Assumption 1 and let $q$ be a Nash equilibrium of the open access game $(F,Q(F\times M),\pi)$ with outputs $s_i=\sum_j q_{ij}$. Define the piecewise linear profile
--
--   $$\bar C_i(s)=\bigl(\partial^+C_i(s_i)\cdot s\bigr)^+,\qquad i=1,\dots,n,$$
--
--   where $\partial^+C_i$ is the right derivative of $C_i$. Then
--
--   1. $\bar C$ satisfies Assumption 1;
--   2. $q$ is also a Nash equilibrium of the open access game under $\bar C$;
--   3. for every Nash equilibrium $q'$ of the open access game under $\bar C$,
--   $$\rho(F\times M,C)=\rho\text{ at }q\text{ under }C\ \le\ \rho\text{ at }q'\text{ under }\bar C=\rho(F\times M,\bar C).$$
--
--   So among cost profiles satisfying Assumption 1, piecewise linear ones are the worst case for the price of anarchy.
--
--   Differences from the source:
--   - encoding: firms 1, …, n and markets 1, …, m → Fin n and Fin m (0-based), supply profile q i j firm first; reason: relabelling only
--   - encoding: the unique Nash equilibrium q^NE → every Nash equilibrium q; reason: Lemma 1 makes the equilibrium unique, so a claim about every equilibrium is the claim about q^NE
--   - encoding: ρ as a real ratio with ρ := 1 when both welfares are 0 → poa in ℝ≥0∞ (x/0 = ⊤ for x > 0); reason: same values wherever the paper's ratio is defined, and no real-division junk value
--   - generalization: ρ(F × M,C) ≤ ρ(F × M,C̄) → adds the conjuncts that C̄ satisfies Assumption 1 and that q is a Nash equilibrium under C̄; reason: both are stated in the proof (Appendix A.1, p.26: "Clearly, C̄i is convex, and differentiable on (0,∞)", "qNE is the unique Nash equilibrium … associated with the cost function profile C̄"); dropping them gives the page's inequality
--   - encoding: ∂⁺Cᵢ, the right derivative → derivWithin (C i) (Set.Ici x) x; reason: Mathlib's derivative within [x, ∞), the right derivative
--   - generalization: n firms and m markets, with n, m ≥ 1 implicit → every n and m in ℕ, including n = 0 and m = 0; reason: the added instances are degenerate, with ρ = 1 on both sides; every instance with n, m ≥ 1 is the page's
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Lemma 2, p.17 (with Appendix A.1, p.26)

import Mathlib
import Definitions.Def_PlatformCournot_Assumption1
import Definitions.Def_PlatformCournot_IsNash
import Definitions.Def_PlatformCournot_poa
import Definitions.Def_PlatformCournot_rightDerivLinearization

namespace PlatformCournot

/-- **Lemma 2: the right-derivative linearization at equilibrium does not decrease the price of
anarchy.**
Pang et al., arXiv:1903.04574v3, Lemma 2, p.17: "Let C = (C1,...,Cn) be a cost function profile
satisfying Assumption 1. Let qNE(F × M) denote the unique Nash equilibrium of the corresponding
networked Cournot game, and define the piecewise linear cost function profile C̄ = (C̄1,...,C̄n)
according to C̄i(si) := (∂+Ci(Σ_{j=1}^m qNE_ij(F × M)) · si)^+ for i = 1,...,n, where ∂+Ci denotes
the right-derivative of the function Ci. It holds that ρ(F × M,C) ≤ ρ(F × M,C̄)."

For a cost profile `C` satisfying Assumption 1 and a Nash equilibrium `q` of the open access game,
the profile `C̄ᵢ(s) = (∂⁺Cᵢ(sᵢ) · s)⁺` satisfies Assumption 1, `q` is a Nash equilibrium for `C̄`
(Appendix A.1, p.26), and every Nash equilibrium `q'` for `C̄` has `ρ` at least that of `q` for `C`.

**Formalization Note** `∂⁺Cᵢ(x)` is `derivWithin (C i) (Set.Ici x) x`. `ρ` is `poa` in `ℝ≥0∞` with
the 0/0 := 1 clause. -/
theorem lemma_2 {n m : ℕ} (D : AffineDemand m) (C : Fin n → ℝ → ℝ) (hC : Assumption1 C)
    (q : Fin n → Fin m → ℝ) (hq : IsNash D C Set.univ q) :
    Assumption1 (rightDerivLinearization C q) ∧
      IsNash D (rightDerivLinearization C q) Set.univ q ∧
      ∀ q', IsNash D (rightDerivLinearization C q) Set.univ q' →
        poa D C q ≤ poa D (rightDerivLinearization C q) q' := by sorry

end PlatformCournot
