-- Prove2me | Theorems.Thm_SVFAppt_eq_9_lower_bound
-- name    : SVFAppt.eq_9_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:48.284997+00:00
-- url     : https://prove2.me/theorems/6c737eb0-5d34-4139-bd2d-d8f23c2754da
-- title:
--   Eq. (9) — the waiting time dominates the positive part of the centred sum
-- statement:
--   Let $B_1,\dots,B_n$ be integrable service times with means $\mu_j$, put $X_j=B_j-\mu_j$, use the mean-based schedule $x=\mu$, and fix a slot $k$ with $k+1\le n$.
--
--   1. For every sequence $\tau$, pathwise,
--   $$W_{k+1}\ \ge\ S_k^+=\big(X_{\tau(1)}+\cdots+X_{\tau(k)}\big)^+.$$
--   2. For every sequence $\sigma$ with $\sigma(i)\le k$ for all $i\le k$ (so that $\{\sigma(1),\dots,\sigma(k)\}=\{1,\dots,k\}$),
--   $$\mathbb EW^{\sigma}_{k+1}\ \ge\ \mathbb E\big(X_1+\cdots+X_k\big)^+ .$$
--   In particular $\mathbb EW^{\mathrm{opt}'}_{k+1}\ge\mathbb E(X_1+\cdots+X_k)^+$, which is (9).
--
--   This is the lower bound on the competitor's waiting time used in the proofs of Theorems 3.3 and 3.4.
--
--   **Formalization Note** 0-based (Lean's $W_k$, $k<n$, is the paper's $W_{k+1}$); $(\cdot)^+$ is `max 0 ·`.
--
--   Differences from the source:
--   - encoding: EW^opt′_{k+1} (the minimum over constrained sequences) → every σ with σ(i) < k for i < k; reason: the minimum over the finite admissible set is attained
--   - generalization: standing assumptions of the paper (independent B_i, Assumption 2.4) → only integrable B_i; no independence or dilation ordering; reason: the inequality uses neither; every instance of the paper satisfies the Lean hypotheses
--   - generalization: service times with means µ_i and variances σ_i² (nonnegative; Remark 2.1 allows negative values) → integrable real-valued service times, possibly negative, variances not assumed finite; reason: variances only label the svf order, which Assumption 2.4 already fixes; every finite-variance nonnegative instance is a special case
--   - encoding: slots and patients numbered 1, …, n → Fin n (0-based); Lean slot i is the paper's slot i + 1; reason: Lean convention; same instances
--   - reading: initial waiting and idle times not stated → W_0 = I_0 = 0 (the paper's W_1 = I_1 = 0); reason: the paper's identity (5) holds exactly under this convention; the first patient arrives to an idle doctor
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, proof of Theorem 3.3, eq. (9), p. 16

import Mathlib
import Definitions.Def_SVFAppt_lindley
import Definitions.Def_SVFAppt_mu

open MeasureTheory

namespace SVFAppt

/-- **Eq. (9): the waiting time dominates the positive part of the centred sum.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, proof of Theorem 3.3, eq. (9), p. 16: "As
Wk+1 = max{0, S1, . . . , Sk}, we have Wk+1 ⩾ S+k = (Xτ(1) + · · · + Xτ(k))+. Note that τ(i) ⩽ k
for all i ⩽ k when we consider EW opt′ k+1, so now EW opt′ k+1 ⩾ E(X1 + · · · + Xk)+."

Let `B 0, …, B (n−1)` be integrable service times on `(Ω, P)`, `X_j = B_j − µ_j`, and fix a
0-based slot `k < n`. Under the mean-based schedule `x = µ`:
1. for every sequence `τ` and every sample point, `W^τ_k ⩾ (X_{τ(0)} + ⋯ + X_{τ(k−1)})^+`;
2. for every sequence `σ` whose first `k` slots hold the patients `0, …, k−1`,
   `E W^σ_k ⩾ E (X_0 + ⋯ + X_{k−1})^+`.

**Formalization Note** 0-based (Lean `W_k` is the paper's `W_{k+1}`). `EW^opt′_{k+1}` is the
minimum over the admissible `σ` of clause 2, attained on the finite set, so clause 2 for every
admissible `σ` is the printed (9). Independence and the dilation ordering are not needed. -/
theorem eq_9_lower_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (B : Fin n → Ω → ℝ) (hBi : ∀ j, Integrable (B j) P) (k : ℕ) (hk : k < n) :
    (∀ (τ : Equiv.Perm (Fin n)) (s : Ω),
      max 0 (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), (B (τ i) s - mu P B (τ i)))
        ≤ wait τ (mu P B) (fun j => B j s) k) ∧
    (∀ σ : Equiv.Perm (Fin n), (∀ i : Fin n, i.val < k → (σ i).val < k) →
      ∫ s, max 0 (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), (B j s - mu P B j)) ∂P
        ≤ ∫ s, wait σ (mu P B) (fun j => B j s) k ∂P) := by sorry

end SVFAppt
