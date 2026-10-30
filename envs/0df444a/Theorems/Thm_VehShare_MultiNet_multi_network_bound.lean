-- Prove2me | Theorems.Thm_VehShare_MultiNet_multi_network_bound
-- name    : VehShare.MultiNet.multi_network_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T04:06:42.621757+00:00
-- url     : https://prove2.me/theorems/3c13d668-2942-4e5d-b3ea-0717f5858ae4
-- title:
--   Any number of networks: some allocation attains $(\sum_c w_c)K/(N+K-1+M)$
-- statement:
--   Let the networks be indexed by a finite nonempty set, with weights $w_c\ge0$, integers $n_c\ge1$ and reals $m_c\ge0$, and let $K\ge0$ be an integer. Then some allocation $(k_c)$ of nonnegative integers with $\sum_c k_c=K$ satisfies
--
--   $$
--   \frac{\big(\sum_c w_c\big)K}{\sum_c n_c+K-1+\sum_c m_c}\le\sum_c\frac{w_ck_c}{n_c+k_c-1+m_c}.
--   $$
--
--   This is the induction on the number of networks on p. 19 ("Assume the inequality holds for $c$, $c\ge2$, then we want to show it also holds for $c+1$"), closed by the case of two networks. With $w_c=p_c$, $n_c=N_c$, $m_c=M_c$ it gives $R(q^s,K^*)/R_s(q^s)\ge K/(N+K-1+M)$.
--
--   **Formalization Note** Every integer is cast to the reals before subtracting $1$; a denominator vanishes only where its numerator is $0$, and Lean's $0/0=0$ is the paper's value.
--
--   Differences from the source:
--   - reading: the induction step for R(q^s,K*)/Rs(q^s) ≥ K/(N+K−1+M) from c to c + 1 networks → the inequality for the maximum over allocations, for any finite nonempty set of networks; reason: the step's chain on p. 19 reduces to this inequality after the availability lower bound; the induction is over the number of networks
--   - generalization: probabilities p_c with Σ p_c = 1 (and division by 1 − p_{c+1}) → weights w_c ≥ 0; reason: scaling gives the paper's form, and the paper's division by 1 − p_{c+1}, undefined when p_{c+1} = 1, is avoided
--   - generalization: C > 2 networks (C = 2 treated separately) → any number C ≥ 1 of networks; reason: C = 1 is immediate and C = 2 is the previous case; the paper's cases are special cases
--   - generalization: N_c locations and workloads M_c of the networks → any integers n_c ≥ 1 and reals m_c ≥ 0; reason: only these properties enter the inequality
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, proof of Theorem 4, case C > 2, p. 19

import Mathlib

namespace VehShare.MultiNet

/-- **Any number of networks.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), proof of Theorem 4, case `C > 2`, p. 19 (induction on the number of networks, closed by the
case `C = 2`).

For a finite nonempty index set of networks with weights `w_c ≥ 0`, integers `n_c ≥ 1` and reals
`m_c ≥ 0`, and every `K ∈ ℕ`, some allocation `k` with `∑_c k_c = K` satisfies
`(∑_c w_c) K / (∑_c n_c + K − 1 + ∑_c m_c) ≤ ∑_c w_c k_c / (n_c + k_c − 1 + m_c)`.

**Formalization Note.** Weights `w_c ≥ 0` in place of probabilities `p_c` with `∑ p_c = 1`
(the paper divides by `1 − p_{c+1}`, undefined when `p_{c+1} = 1`); any number `C ≥ 1` of networks
(`Nonempty`, as in the paper; `C = 1` and `C = 2` included). Casts to `ℝ` before `− 1`;
`0/0 = 0` only where the numerator is 0. -/
theorem multi_network_bound {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → ℝ)
    (hw : ∀ c, 0 ≤ w c) (n : ι → ℕ) (hn : ∀ c, 1 ≤ n c) (m : ι → ℝ) (hm : ∀ c, 0 ≤ m c)
    (K : ℕ) :
    ∃ k : ι → ℕ, ∑ c, k c = K ∧
      (∑ c, w c) * K / ((∑ c, (n c : ℝ)) + K - 1 + ∑ c, m c) ≤
        ∑ c, w c * k c / ((n c : ℝ) + k c - 1 + m c) := by sorry

end VehShare.MultiNet
