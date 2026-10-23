-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_recursion_invariant
-- name    : SKAlgorithm.Qudit.recursion_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:55.566854+00:00
-- url     : https://prove2.me/theorems/94320503-7227-46d6-b538-50f471956774
-- title:
--   Eqs. (1)–(2), (15), (21)–(22) — the Solovay-Kitaev recursion returns ε_n-approximations of length ≤ 5ⁿ l₀
-- statement:
--   Fix $d$ and constants $c_{gc'}, c_{gc''} > 0$. There are constants $c > 0$ and $\epsilon^\ast > 0$ with the following property. Let $\mathcal G \subseteq SU(d)$ be finite and closed under $g \mapsto g^\dagger$, let $0 < \epsilon_0 \le \epsilon^\ast$ and $l_0 \in \mathbb N$, and let $\epsilon_n$ be defined by $\epsilon_n = c\, \epsilon_{n-1}^{3/2}$ (Eq. (1)). Suppose
--
--   1. the lookup routine returns, for every $U \in SU(d)$, a sequence $\mathrm{basic}(U)$ of gates from $\mathcal G$ of length at most $l_0$ with $d(U, \mathrm{basic}(U)) < \epsilon_0$;
--   2. the decomposition routine, at every level $k$, returns for every $\Delta \in SU(d)$ with $d(I, \Delta) < \epsilon_k$ a pair $(V, W) = \mathrm{gc}_k(\Delta)$ in $SU(d)$ with
--   $$d(VWV^\dagger W^\dagger, \Delta) < c_{gc'}\, \epsilon_k^{3/2}, \qquad d(I, V),\ d(I, W) < c_{gc''} \sqrt{\epsilon_k} .$$
--
--   Then for every $n$ and every $U \in SU(d)$ the sequence $U_n = \mathrm{SK}(U, n)$ consists of gates from $\mathcal G$, has length at most $5^n l_0$ (Eq. (2), $l_n = 5 l_{n-1}$), and
--   $$d(U, U_n) < \epsilon_n .$$
--
--   This is the accuracy and length analysis of the qudit algorithm: Lemma 1 bounds the error of the approximate commutator (Eq. (15)) and the triangle inequality (Eqs. (21)–(22)) gives $\epsilon_n = (c_{gc'} + c_{\mathrm{approx}})\epsilon_{n-1}^{3/2}$.
--
--   **Formalization Note.** The constant $c$ plays the role of $c_{gc'} + c_{\mathrm{approx}}$ and is existential (the paper estimates $c_{\mathrm{approx}} \approx 8c_{gc''}$ only approximately); $c$ and $\epsilon^\ast$ depend on $c_{gc'}, c_{gc''}$ (and possibly $d$) only, and are chosen before $\mathcal G$, $\epsilon_0$, $l_0$ and the routines. The threshold $\epsilon_0 \le \epsilon^\ast$ is the paper's requirement $\epsilon_0 < 1/c_{\mathrm{approx}}^2$ (p. 6) that makes the accuracies decrease. The length bound is Eq. (2) unrolled. The decomposition routine is indexed by the level (see the definition file).
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 6, Eqs. (1)–(2) and 'we must have ǫ0 < 1/c²approx'; p. 9, Eq. (15); p. 11, Eqs. (21)–(22)

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem recursion_invariant (d : ℕ) (c' c'' : ℝ) (hc' : 0 < c') (hc'' : 0 < c'') :
    ∃ c εs : ℝ, 0 < c ∧ 0 < εs ∧
      ∀ (G : Finset (SU d)), (∀ g ∈ G, g⁻¹ ∈ G) →
      ∀ (ε₀ : ℝ) (l₀ : ℕ), 0 < ε₀ → ε₀ ≤ εs →
      ∀ (basic : SU d → List (SU d)) (gc : ℕ → SU d → SU d × SU d),
        (∀ U : SU d, (∀ g ∈ basic U, g ∈ G) ∧ (basic U).length ≤ l₀ ∧
          opDist U (seqUnitary (basic U)) < ε₀) →
        (∀ (k : ℕ) (Δ : SU d), opDist 1 Δ < epsSeq c ε₀ k →
          opDist ((gc k Δ).1 * (gc k Δ).2 * (gc k Δ).1⁻¹ * (gc k Δ).2⁻¹) Δ <
              c' * epsSeq c ε₀ k ^ ((3 : ℝ) / 2) ∧
            opDist 1 (gc k Δ).1 < c'' * Real.sqrt (epsSeq c ε₀ k) ∧
            opDist 1 (gc k Δ).2 < c'' * Real.sqrt (epsSeq c ε₀ k)) →
        ∀ (n : ℕ) (U : SU d),
          (∀ g ∈ solovayKitaev basic gc n U, g ∈ G) ∧
          (solovayKitaev basic gc n U).length ≤ 5 ^ n * l₀ ∧
          opDist U (seqUnitary (solovayKitaev basic gc n U)) < epsSeq c ε₀ n := by sorry

end SKAlgorithm.Qudit
