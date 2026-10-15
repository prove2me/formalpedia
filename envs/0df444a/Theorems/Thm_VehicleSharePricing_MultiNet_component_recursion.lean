-- Prove2me | Theorems.Thm_VehicleSharePricing_MultiNet_component_recursion
-- name    : VehicleSharePricing.MultiNet.component_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:13.087236+00:00
-- url     : https://prove2.me/theorems/9fca50be-6967-4fde-9e7b-9aa9fa0231fe
-- title:
--   §6, proof of Theorem 4, p. 18 — recursion (5) on each network: $\alpha(q^s,K_c,N_c)=K_c/(N_c+K_c-1+(1-\alpha(q^s,K_c-1,N_c))M_c)$
-- statement:
--   Work in the setting of §6 of Benjaafar and Shen: $q^s$ is an optimal solution of Problem (2) with workload budget $\Delta\ge K$, it splits the locations into connected networks $c$ (with location sets $\mathcal N_c$, $N_c=|\mathcal N_c|$ locations and pair sets $\mathcal A_c$), and $r$ is a positive solution of the traffic equations (9). Let $\alpha(q^s,K_c,N_c)$ denote the availability at a location $i\in\mathcal N_c$ when network $c$ holds $K_c$ vehicles, and let
--   $$M_c=\sum_{(i,j)\in\mathcal A_c}\frac{\Lambda_{ij}}{\mu_{ij}}q^s_{ij}.$$
--   Then for every network $c$, every location $i\in\mathcal N_c$ and every $K_c\ge1$,
--   $$\alpha(q^s,K_c,N_c)=\frac{K_c}{N_c+K_c-1+\big(1-\alpha(q^s,K_c-1,N_c)\big)M_c}.$$
--
--   This is Equation (5) of the paper applied to each network separately. Since $\alpha(q^s,0,N_c)=0$, the recursion determines the availability of network $c$ for every number of vehicles; in particular it is the same at every location of the network, which is what makes the notation $\alpha(q^s,K_c,N_c)$ meaningful.
--
--   **Formalization Note** The availability is the BCMP product form of the network on its own (see the model file). The paper states (5) for a strongly connected network (p. 8) and proves it in the Appendix (pp. 23–24); here it is stated for each class of the split. $K_c-1$ is natural-number subtraction, used only under $K_c\ge1$. The hypothesis that $q^s$ is optimal is the paper's; the identity itself uses only balance, the split and (9).
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 18, §6, proof of Theorem 4 (recursive relationship for α(q^s,K_c,N_c)); Equation (5), p. 8; Appendix, pp. 23–24

import Mathlib
import Definitions.Def_VehicleSharePricing_MultiNet_Model

namespace VehicleSharePricing.MultiNet

/-- §6, proof of Theorem 4, p. 18: Equation (5) on each connected network `c`.
For every location `i` of network `c` and every `Kc ≥ 1`,
`α(q^s, Kc, N_c) = Kc / (N_c + Kc - 1 + (1 - α(q^s, Kc - 1, N_c)) M_c)`. -/
theorem component_recursion {L ι : Type*} [Fintype L] [DecidableEq L] [Nonempty L] [Fintype ι] [DecidableEq ι]
    (Λ μ : L → L → ℝ) (I : L → L → ℝ → ℝ) (Δ : ℝ) (K : ℕ) (q : L → L → ℝ) (r : L → ℝ)
    (comp : L → ι) (h : SplitStaticSetting Λ μ I Δ K q r comp)
    (c : ι) (i : ClassLoc comp c) (Kc : ℕ) (hKc : 1 ≤ Kc) :
    classAvail Λ μ q r comp c Kc i =
      (Kc : ℝ) / ((classSize comp c : ℝ) + (Kc : ℝ) - 1 +
        (1 - classAvail Λ μ q r comp c (Kc - 1) i) * classWorkload Λ μ q comp c) := by sorry

end VehicleSharePricing.MultiNet
