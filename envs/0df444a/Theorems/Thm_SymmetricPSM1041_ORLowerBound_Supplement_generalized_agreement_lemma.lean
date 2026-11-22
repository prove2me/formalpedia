-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_generalized_agreement_lemma
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.generalized_agreement_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T03:46:10.576109+00:00
-- url     : https://prove2.me/theorems/857bb4ca-b8bb-4c53-b167-d9674eb4a4b2
-- title:
--   Lemma 18 — generalized agreement lemma
-- statement:
--   For every fixed $a>0$ there is $c>0$, depending only on $a$, with the following property. Let $1\le p\le n$ be integers, $\Sigma$ a finite alphabet, and $\alpha_S:S\to\Sigma$ a coloring for every $S\subseteq[n]$. Let
--
--   $$S_1\subsetneq S_2\subsetneq\cdots\subsetneq S_\ell,\qquad |S_i|=p+i,\qquad \ell\ge a\sqrt p,$$
--
--   and suppose that for all $i<j$ the functions $\alpha_{S_i}$ and $\alpha_{S_j}|_{S_i}$ disagree on more than $p$ points. Then
--
--   $$|\Sigma|\ge c\sqrt p.$$
--
--   This is the source's $|\Sigma|=\Omega_a(\sqrt p)$. The lemma drives the alphabet lower bounds for exact majority and modular counting (Theorems 23 and 24).
--
--   **Formalization Note** The chain is a strictly increasing map from `Fin ℓ` (index $i-1$) to finite subsets of `Fin n`. The disagreement count is taken over points lying in both sets, which for $S_i\subseteq S_j$ is the set of points of $S_i$.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: an arbitrary finite alphabet Σ → a finite type Sig in an arbitrary universe; reason: every finite set is in bijection with a finite type; only |Σ| enters the statement
--   - encoding: |Σ| = Ω_a(√p) → ∃ c > 0 depending only on a, with c·√p ≤ |Σ| for every p ≥ 1 (no threshold on p); reason: for p below any threshold P0 the hypotheses force ℓ ≥ 1 and hence Σ nonempty, so |Σ| ≥ 1 ≥ √p/√P0; shrinking c removes the threshold, so the two forms are equivalent
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 14, Lemma 18 (proof p. 14)

import Mathlib

namespace SymmetricPSM1041.ORLowerBound.Supplement

open Classical in
theorem generalized_agreement_lemma :
    ∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧
      ∀ n p : ℕ, 1 ≤ p → p ≤ n →
      ∀ (Sig : Type*) [Fintype Sig],
      ∀ α : (S : Finset (Fin n)) → (i : Fin n) → i ∈ S → Sig,
      ∀ ℓ : ℕ, a * Real.sqrt p ≤ ℓ →
      ∀ Sq : Fin ℓ → Finset (Fin n), StrictMono Sq →
        (∀ i : Fin ℓ, (Sq i).card = p + (i.val + 1)) →
        (∀ i j : Fin ℓ, i < j →
          p < (Finset.univ.filter (fun t : Fin n => ∃ (hti : t ∈ Sq i) (htj : t ∈ Sq j),
            α (Sq i) t hti ≠ α (Sq j) t htj)).card) →
        c * Real.sqrt p ≤ (Fintype.card Sig : ℝ) := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
