-- Prove2me | Theorems.Thm_QCollLB_lemma_7_1
-- name    : QCollLB.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:17:51.563597+00:00
-- url     : https://prove2.me/theorems/8ead91b4-b594-42ae-a986-933688295ace
-- title:
--   Lemma 7.1 — probability of recording prescribed values
-- statement:
--   Fix $k\ge1$. There is a constant $C_k$ such that the following holds. Let $n\ge2k$ and let $t$ be an integer with $0\le t<n/2$. Let $S\subseteq[n]$ be a fixed set with $|S|\le t$ and let $h:S_n\to\mathbb C$ depend only on $\pi|_S$ with $\|h\|_\infty\le1$. Then for every fixed $k$-set $B\subseteq[n]$,
--   $$
--   \|P_BVh\|^2\le C_k\Big(\frac t{n-t+1}\Big)^k ,
--   $$
--   and for $t=0$ the left side is zero. Here $h$ is identified with $n!^{-1/2}\sum_\pi h(\pi)|\pi\rangle$ and $P_B$ asserts $B\subseteq\mathrm{Im}\,d$.
--
--   This is the one-round recording bound: a bounded function of $t$ fixed positions has encoded weight $O_k((t/n)^k)$ on databases containing $k$ prescribed values.
--
--   Differences from the source:
--   - encoding: h identified with n!^{−1/2}Σh(π)|π⟩ (proof, p.54) → funVec h; reason: the identification printed in the proof
--   - encoding: t < n/2 → 2t < n; reason: same instances
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 7.1, Eq. (73), p.52

import Mathlib
import Definitions.Def_QCollLB_Harmonic

namespace QCollLB

open CompPermOracle

/-- **Lemma 7.1 (Probability of recording prescribed values)** (Peng–Wu, arXiv:2611.01767 (PDF
sha256 4e5aba34…d9fc), Lemma 7.1, Eq. (73), p.52). Fix `k ≥ 1`. There is a constant `C_k` such that
for `n ≥ 2k`, every integer `0 ≤ t < n/2`, every fixed `S ⊆ [n]` with `|S| ≤ t`, every `h : S_n → ℂ`
depending only on `π|_S` with `‖h‖_∞ ≤ 1`, and every fixed `k`-set `B ⊆ [n]`,
`‖P_B V h‖² ≤ C_k (t/(n − t + 1))^k`; for `t = 0` the left side is zero.

**Formalization Note.** `h` is identified with `n!^{−1/2} Σ_π h(π)|π⟩ ∈ P` (`funVec h`, proof of
Lemma 7.1, p.54). `P_B` is the diagonal projector asserting `B ⊆ Im d` (p.52). `C_k` is chosen before
`n, t, S, h, B`; `t < n/2` is `2t < n`. -/
theorem lemma_7_1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ (n t : ℕ), 2 * k ≤ n → 2 * t < n →
      ∀ (S : Finset (Fin n)), S.card ≤ t →
      ∀ h : Equiv.Perm (Fin n) → ℂ,
        (∀ π π' : Equiv.Perm (Fin n), (∀ i ∈ S, π i = π' i) → h π = h π') →
        (∀ π, ‖h π‖ ≤ 1) →
      ∀ B : Finset (Fin n), B.card = k →
        ‖PB B (V n (funVec h))‖ ^ 2 ≤ C * ((t : ℝ) / ((n : ℝ) - t + 1)) ^ k ∧
          (t = 0 → ‖PB B (V n (funVec h))‖ ^ 2 = 0) := by sorry

end QCollLB
