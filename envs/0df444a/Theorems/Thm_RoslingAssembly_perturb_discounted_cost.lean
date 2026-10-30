-- Prove2me | Theorems.Thm_RoslingAssembly_perturb_discounted_cost
-- name    : RoslingAssembly.perturb_discounted_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:50:28.080923+00:00
-- url     : https://prove2.me/theorems/b5d6387e-1b5d-4de1-847d-1cdb49c49d37
-- title:
--   Discounted cost of the perturbed policy (corrected: backlog term for the end item)
-- statement:
--   Let $0<\alpha<1$, let $\pi$ be a non-anticipating measurable policy with finite discounted cost at $\alpha$, let $i$ be an item, $n$ a real number, $S=\{i\}\cup B(i)$ and $M_m=\max_{k\in S}M_k$, and let $\pi'$ be the perturbed policy that adds $n$ units of every $k\in S$ from period $M_m-M_k+1$ on. Then $\pi'$ has finite discounted cost at $\alpha$ and
--   $$J_\alpha(\pi')=J_\alpha(\pi)+n\,\alpha^{M_m}\,\frac{h_i\alpha^{-M_{s(i)}}+\sum_{k\in B(i)}h_k\alpha^{-M_{s(k)}}}{1-\alpha}+\alpha^{l_1}(p+H_1)\,D,$$
--   $$D=\sum_{t\ge1}\alpha^{t-1}\,\mathbb E\big[G_{l_1}(Y'_{1t})-G_{l_1}(Y_{1t})\big],$$
--   where $G_{l_1}$ is the expected backlog function. Moreover $D=0$ unless $i$ is the end item.
--
--   The middle term is $n$ times the paper's total cost increase $\alpha^{l_i}(h_i+\sum_{k\in B(i)}h_k\alpha^{-(M_{s(k)}-M_{s(i)})})/(1-\alpha)$, capitalized from period $M_m-M_i+1$ to period $1$.
--
--   **Formalization Note** Standing demand assumptions as in problem P.
--
--   Differences from the source:
--   - correction: the total cost increase of the alternative policy is α^{l_i}(h_i + Σ_{k∈B(i)} h_k α^{−(M_{s(k)}−M_{s(i)})})/(1 − α) per unit (holding costs only) → the change of J is n times that (capitalized to period 1) plus α^{l_1}(p + H_1) D, where D is the change of the discounted expected backlog, and D = 0 unless i is the end item; reason: for the end item the extra units also lower the backlog: N = 1, l_1 = 0, H_1 = −1, p = 2, ξ exponential with mean 1, history Y_{1,0} = ξ_0 = 0, π the order-nothing policy, n = 1 give D < 0 since G is strictly decreasing, so the change of J differs from the printed increase; Theorem 4(i) is unaffected because −E G(Y_1t) ≤ G(Y'_1t) − G(Y_1t) ≤ 0
--   - generalization: one more unit → n units, any real n; reason: n = 1 is the paper's case
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
--   - encoding: decisions Y_it dependent on system history up to period t; objective E{Σ_t α^{t−1}(…)} → deterministic measurable functions of ξ_1, …, ξ_{t−1} on the canonical i.i.d. space, (3) on every demand path, objective Σ_t α^{t−1} E[c_t] for policies with Σ_t α^{t−1} E|c_t| < ∞ (`Admissible`); reason: restricting the policies that witness an existence claim only strengthens it; for such policies Σ_t E = E Σ_t (Fubini)
--   - encoding: ξ_t ≥ 0 i.i.d. with density φ and mean λ > 0; φ_1^{l_1+1} the (l_1 + 1)-fold convolution → law μ with μ(−∞, 0) = 0, μ ≪ Lebesgue, ∫|x| dμ < ∞, ∫ x dμ > 0, on (ℕ → ℝ, `Measure.infinitePi`); ∫_y^∞ (ξ − y) φ^{l_1+1}(ξ) dξ written as E[(ξ_1 + … + ξ_{l_1+1} − y)^+] under `Measure.pi`; reason: same objects
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, Appendix B, Proof of Theorem 4, p. 578 (unnumbered, 'So, the total cost increase is')

import Mathlib
import Definitions.Def_RoslingAssembly_IsPolicy
import Definitions.Def_RoslingAssembly_Admissible
import Definitions.Def_RoslingAssembly_discCost
import Definitions.Def_RoslingAssembly_perturb
import Definitions.Def_RoslingAssembly_Network_Ms
open MeasureTheory

namespace RoslingAssembly

/-- **Discounted cost of the perturbed policy** (Appendix B, Proof of Theorem 4, p. 578,
unnumbered). Rosling, *Optimal Inventory Policies for Assembly Systems under Random Demands*,
Operations Research 37(4), 1989, p. 578: "So, the total cost increase is α^{l_i}(h_i +
Σ_{k∈B(i)} h_k · α^{−(M_{s(k)}−M_{s(i)})}) / (1 − α) < 0 by assumption."

Let `0 < α < 1`, let `pol` be a non-anticipating measurable policy with finite discounted cost at
`α`, let `i` be an item, `n` a real number, `S = {i} ∪ B(i)` and `M_m = max_{k∈S} M_k`. Then the
perturbed policy `pol'` (`perturb net ℓ pol i n`) has finite discounted cost at `α`, and
$$J_\alpha(\pi')=J_\alpha(\pi)+n\,\alpha^{M_m}\,
\frac{h_i\alpha^{-M_{s(i)}}+\sum_{k\in B(i)}h_k\alpha^{-M_{s(k)}}}{1-\alpha}
+\alpha^{l_1}(p+H_1)\,D,\qquad
D=\sum_{t\ge1}\alpha^{t-1}\,\mathbb E\big[G(Y'_{1t})-G(Y_{1t})\big],$$
where `G = backlogG μ l_1` is the expected backlog function; moreover `D = 0` unless `i` is the
end item. The middle term is `n` times the paper's total cost increase, capitalized from period
`M_m − M_i + 1` to period 1 (a factor `α^{M_m − M_i}`).

**Formalization Note.** The end item (paper item 1) is Lean item `0`; for it the extra units also
lower the backlog, which the printed proof does not mention: that is the term `D`. Sum index
`t : ℕ` is paper period `t + 1`. Standing demand assumptions as in the model. -/
theorem perturb_discounted_cost {N : ℕ} [NeZero N] (net : Network N) (ℓ : Fin N → ℕ)
    (H : Fin N → ℝ) (p : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμac : μ ≪ volume) (hμi : Integrable (fun x => x) μ)
    (hlam : 0 < ∫ x, x ∂μ) (Yh : ℤ → Fin N → ℝ) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) (hpol : IsPolicy pol)
    (hadm : Admissible net ℓ H p μ Yh pol α) (i : Fin N) (n : ℝ) :
    Admissible net ℓ H p μ Yh (perturb net ℓ pol i n) α ∧
      discCost net ℓ H p μ Yh (perturb net ℓ pol i n) α =
        discCost net ℓ H p μ Yh pol α +
          n * α ^ ((insert i (net.B i)).sup' (Finset.insert_nonempty _ _) (net.M ℓ)) *
            (net.h H i * α ^ (-(net.Ms ℓ i : ℤ)) +
              ∑ k ∈ net.B i, net.h H k * α ^ (-(net.Ms ℓ k : ℤ))) / (1 - α) +
          α ^ ℓ 0 * (p + H 0) *
            ∑' t : ℕ, α ^ t * ∫ ω,
              (backlogG μ (ℓ 0) (Ypath Yh (perturb net ℓ pol i n) ω ((t : ℤ) + 1) 0) -
                backlogG μ (ℓ 0) (Ypath Yh pol ω ((t : ℤ) + 1) 0)) ∂(pathMeasure μ) ∧
      (i ≠ 0 →
        ∑' t : ℕ, α ^ t * ∫ ω,
          (backlogG μ (ℓ 0) (Ypath Yh (perturb net ℓ pol i n) ω ((t : ℤ) + 1) 0) -
            backlogG μ (ℓ 0) (Ypath Yh pol ω ((t : ℤ) + 1) 0)) ∂(pathMeasure μ) = 0) := by sorry

end RoslingAssembly
