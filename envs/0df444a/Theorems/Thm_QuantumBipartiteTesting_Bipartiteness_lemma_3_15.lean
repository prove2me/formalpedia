-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_15
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:54.274002+00:00
-- url     : https://prove2.me/theorems/fe6da4a4-0e3c-4d7a-b2e1-d4b1fa3891e9
-- title:
--   Lemma 3.15 — explicit reciprocal on the whole rectangle
-- statement:
--   Let $q(N)$ be any natural-valued family with $q(N)=o(N^{1/3})$. For the explicit repeated-factor truncation in equation (20), eventually in $N$,
--   $$\deg A_{q(N)}\le J_{q(N)}=4d_{q(N)}+10,$$
--   $$|D_{q(N)}(M,\ell)A_{q(N)}(M,\ell)-1|\le10^{-2}$$
--   for every real $1\le\ell\le R$ and $|M-M_0|\le R^{3/2}$. The truncation degrees have a single universal $O(q\log q)$ bound, expressed with a globally defined small-query convention. The theorem concerns the constructed polynomial, not a freely chosen approximant, and retains the entire real rectangle.
--
--   Differences from the source:
--   - encoding: degree O(q log q) → a positive universal multiple of 1 + q log(q+2); reason: the two rates agree as q tends to infinity; the globally defined expression also retains q=0 and q=1 without artificial hypotheses
--   - encoding: suppose q=o(N^(1/3)) → quantify every natural-valued family q(N), using IsLittleO at infinity and one eventual threshold; reason: the source hypothesis is asymptotic, not a property of one isolated pair q,N
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 3.15, PDF = printed page 19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_3_15 :
    (∃ Cdeg : ℝ, 0 < Cdeg ∧ ∀ q : ℕ,
      (TruncationDegree q : ℝ) ≤ Cdeg * DegreeScale q) ∧
    (∀ q : ℕ → ℕ,
      Asymptotics.IsLittleO Filter.atTop (fun N => (q N : ℝ)) (fun N => (N : ℝ)^(1/3 : ℝ)) →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (ReciprocalPolynomial N (q N)).totalDegree ≤ TruncationDegree (q N) ∧
        ∀ M l : ℝ, Rectangle N M l →
          |Eval (Denominator (q N)) M l * Eval (ReciprocalPolynomial N (q N)) M l - 1| ≤ 1/100) := by sorry

end QuantumBipartiteTesting.Bipartiteness
