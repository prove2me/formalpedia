-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_corollary_e_2
-- name    : PrefixMixLearn.Proper.corollary_e_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:45:46.918407+00:00
-- url     : https://prove2.me/theorems/e55dc1ee-3084-49d1-949d-fd0bef25d164
-- title:
--   Corollary E.2 — transfer of the test advantage to the clean two-component gap (q_h − q_k)(b − a)
-- statement:
--   Let $P_h,P_k$ be full-support laws on $\{0,1\}^d$, $M_h=(1-q_h)Q_\nu+q_hQ_\mu$, $M_k=(1-q_k)Q_\nu+q_kQ_\mu$ with $q_h,q_k\in[0,1]$, $\eta_h=d_{TV}(P_h,M_h)$, $\eta_k=d_{TV}(P_k,M_k)$, and let $e$ be the acceptance kernel of Theorem E.1 applied with $P_h$ as first and $P_k$ as second teacher at accuracy $\xi$, with $a=E_{Q_\nu}e$, $b=E_{Q_\mu}e$. Then
--   $$(q_h-q_k)(b-a)\ge|q_h-q_k|\,d_{TV}(Q_\mu,Q_\nu)-2(\eta_h+\eta_k)-\xi.$$
--   In the Lean statement $e$ is any $[0,1]$-valued kernel with the advantage property (E.1) for these teachers, which includes the kernel of Theorem E.1. It turns the test's advantage into a lower bound on the clean gap $b-a$ used by the unmixing.
--
--   Differences from the source:
--   - generalization: e is the acceptance kernel of Theorem E.1's test with teachers P_h, P_k → e is any kernel with values in [0,1] satisfying E_{P_h} e − E_{P_k} e ≥ d_TV(P_h, P_k) − ξ; reason: Theorem E.1's kernel has values in [0,1] and satisfies (E.1), so the statement specializes to the source's
--   - generalization: P_h, P_k the suffix laws of the target at fixed equal-length prefixes h, k → any full-support laws P_h, P_k on {0,1}^d; reason: suffix laws of a full-support target are full-support laws, so this specializes to the source's
--   - encoding: Q_ν, Q_μ product laws on the suffix → ν, μ ∈ [0,1]^d; reason: the parameter range of a product law
--   - reading: all quantities are interpreted conditionally on any earlier history fixing h, k and the test parameters → the kernel and the laws are fixed inputs of the statement; reason: conditioning on that history fixes them
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 38 (PDF 40), Corollary E.2, (E.4)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws

namespace PrefixMixLearn.Proper

/-- Corollary E.2 (transfer to a clean two-component suffix): let `M_h = (1 − q_h)Q_ν + q_hQ_μ`,
`M_k = (1 − q_k)Q_ν + q_kQ_μ`, `η_h = d_TV(P_h, M_h)`, `η_k = d_TV(P_k, M_k)`, and let `e` be a
`[0,1]`-valued kernel with the advantage (E.1) for the teachers `P_h` (first) and `P_k` (second),
`a = E_{Q_ν} e`, `b = E_{Q_μ} e`. Then
`(q_h − q_k)(b − a) ≥ |q_h − q_k| d_TV(Q_μ, Q_ν) − 2(η_h + η_k) − ξ` (E.4). -/
theorem corollary_e_2 (d : ℕ) (hd : 1 ≤ d) (Ph Pk : Cube d → ℝ) (hPh : IsLaw Ph)
    (hPhf : FullSupport Ph) (hPk : IsLaw Pk) (hPkf : FullSupport Pk)
    (qh qk : ℝ) (hqh : 0 ≤ qh ∧ qh ≤ 1) (hqk : 0 ≤ qk ∧ qk ≤ 1)
    (ν μ : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i ∧ ν i ≤ 1) (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1)
    (e : Cube d → ℝ) (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1)
    (hadv : tv Ph Pk - ξ ≤ ∑ x, Ph x * e x - ∑ x, Pk x * e x) :
    |qh - qk| * tv (prodLaw μ) (prodLaw ν) - 2 * (tv Ph (mixLaw qh ν μ) + tv Pk (mixLaw qk ν μ))
        - ξ ≤
      (qh - qk) * (∑ x, prodLaw μ x * e x - ∑ x, prodLaw ν x * e x) := by sorry

end PrefixMixLearn.Proper
