-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_Supplement_polynomial_field_evasive_sets
-- name    : SubspaceEvasion312.Explicit.Supplement.polynomial_field_evasive_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:47:48.596991+00:00
-- url     : https://prove2.me/theorems/55153ddd-41d5-4e52-9c28-5be375b0d298
-- title:
--   Theorem 25 — explicit subspace evasive sets over polynomially large fields
-- statement:
--   Write $\ell_A=\lceil50r^2/\varepsilon\rceil$, $\ell_B=\lceil256r(1+\log_2(r/\varepsilon))/\varepsilon\rceil$ and $L=L(r,\varepsilon)=\min(2\ell_A,2\ell_B)$. The statement has two parts.
--
--   1. **Shape of $L$.** For all integers $r\ge1$ and $\varepsilon\in(0,1)$ with $r/\varepsilon\ge2$,
--   $$L(r,\varepsilon)\le1028\min\Big(\frac{r^2}{\varepsilon},\frac{r\log_2(r/\varepsilon)}{\varepsilon}\Big).$$
--   2. **Construction.** For every real $C>0$ there is a constant $K$, depending only on $C$, such that for all integers $r\ge1$ and $\varepsilon\in(0,1)$ there is a threshold $N_0$ with the following property. For every finite field $\mathbb F_q$ there are an ordering of $\mathbb F_q$ and two register programs (an indexer and a membership tester), fixed for the field, such that for every $n\ge N_0$ with $q\le n^C$ there is a set $A\subseteq\mathbb F_q^n$ with
--      - $A$ is $(r,L)$ subspace evasive: every $\mathbb F_q$-linear subspace of dimension at most $r$ meets $A$ in at most $L$ points;
--      - $|A|\ge q^{(1-\varepsilon)n}$;
--      - the indexer, given $n$ and the base-$q$ digits of $i<|A|$, outputs the $i$-th element of $A$ under a bijection, and the membership tester, given $n$ and $y\in\mathbb F_q^n$, outputs $1$ if $y\in A$ and $0$ otherwise, each within charged time and word bound $n^{K\,r\,L}$.
--
--   Unlike Theorem 24, the field may grow with $n$, up to any fixed polynomial size, and $N_0$ does not depend on $q$.
--
--   **Formalization Note** $L$ uses the constants of the proof sketch (Case A with Corollary 21, Case B with Corollary 22, $L=2\ell$). Time is measured in the mission's published register machine (field operations one step, program size charged).
--
--   Differences from the source:
--   - reading: L = O(min(r²/ε, r log(r/ε)/ε)) → L = min(2⌈50r²/ε⌉, 2⌈256r(1+log₂(r/ε))/ε⌉), and L ≤ 1028·min(r²/ε, r log₂(r/ε)/ε) whenever r/ε ≥ 2; reason: the proof's explicit Case A and Case B values; a raw log bound with an absolute constant fails near r = 1, ε → 1, where r log(r/ε)/ε → 0 while L ≥ 1 for a nonempty evasive set
--   - reading: explicit set; membership oracle with running time n^{O_C(rL)} → indexed construction and membership programs, fixed per field and uniform in n, with charged time and word bound n^{K r L}, K depending only on C; reason: the proof sketch bounds both the construction and the membership oracle by n^{O(rL)}; printed p. 7 defines constructable and membership time
--   - encoding: every prime power q ≤ n^C, A ⊆ F_q^n → every finite field F with (card F : ℝ) ≤ n^C, A : Set (Vec F n); reason: finite fields are exactly the F_q
--   - encoding: bijection {1, …, |A|} → A → bijection from Fin |A| (indices 0, …, |A|−1, input as d base-q digits with q^d ≥ |A|); reason: a shift of the index range; digits keep machine words polynomial
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, Explicit Subspace Evasive Sets via Subspace Designs, STOC 2027 submission #312 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf, PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc, Theorem 25, printed p. 13 (PDF p. 14), with the constants of its proof sketch on the same page

import Definitions.Def_SubspaceEvasion312_Explicit_Supplement_codes

namespace SubspaceEvasion312.Explicit.Supplement
open Classical
/-- Theorem 25, printed p.13 (PDF p.14). The field may vary with n (every finite
field with q <= n^C); the threshold N0 depends on r, eps, C only, and the exponent
constant K on C only. The list bound is the proof's 2 ceil(50 r^2/eps) or
2 ceil(256 r (1+log2(r/eps))/eps), whichever is smaller, with its uniform O-shape
on the tail r/eps >= 2. Construction (indexed bijection) and membership are charged
programs, fixed for each field and uniform in n. -/
theorem polynomial_field_evasive_sets :
    (∀ (r : ℕ) (ε : ℝ), 0 < r → 0 < ε → ε < 1 → 2 ≤ (r : ℝ) / ε →
      (polyFieldBound r ε : ℝ) ≤ 1028 * asymptoticShape r ε) ∧
    ∀ C : ℝ, 0 < C → ∃ K : ℕ, 0 < K ∧
    ∀ (r : ℕ) (ε : ℝ), 0 < r → 0 < ε → ε < 1 → ∃ N₀ : ℕ, 0 < N₀ ∧
    ∀ (F : Type) [Field F] [Fintype F],
    ∃ (alphabet : Fin (Fintype.card F) ≃ F) (index member : Program F),
    ∀ N ≥ N₀, (Fintype.card F : ℝ) ≤ (N : ℝ) ^ C →
    ∃ A : Set (Vec F N),
      Evasive (F := F) A r (polyFieldBound r ε) ∧
      (Fintype.card F : ℝ) ^ ((1 - ε) * N) ≤ (A.ncard : ℝ) ∧
      Constructable A alphabet index [N]
        (N ^ (K * r * polyFieldBound r ε)) (N ^ (K * r * polyFieldBound r ε)) ∧
      ∀ y : Vec F N, RunsWithin member [N] (vectorData y)
        (N ^ (K * r * polyFieldBound r ε)) (N ^ (K * r * polyFieldBound r ε))
        [if y ∈ A then 1 else 0] := by sorry
end SubspaceEvasion312.Explicit.Supplement
