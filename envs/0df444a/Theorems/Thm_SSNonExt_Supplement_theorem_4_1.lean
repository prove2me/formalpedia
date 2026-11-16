-- Prove2me | Theorems.Thm_SSNonExt_Supplement_theorem_4_1
-- name    : SSNonExt.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T18:57:46.539228+00:00
-- url     : https://prove2.me/theorems/01f89108-7fab-45c0-beca-5958e5563cd0
-- title:
--   Theorem 4.1 — perfect two-out-of-$n$ sharing on flat sources with extraction error $\ge 1/(4n-2)$, tight
-- statement:
--   Let $n\ge2$ and let $b$ satisfy $2^b>n$. Let $V=\mathbb F_{2^b}$ and let $\alpha_1,\dots,\alpha_n\in V$ be distinct and nonzero. Let $\Pi_{b,n}$ be the two-out-of-$n$ scheme of display (5) with key set $\mathcal K_n$, and $\mathcal S_{b,n}=\{P_T:T\subseteq V\}$ its source class of display (6). Then $\Pi_{b,n}$ is a **perfectly correct** two-out-of-$n$ scheme for $b$-bit messages (every set of at least two parties reconstructs the message from its shares, for every message and every key) that is **perfectly private** for $\mathcal S_{b,n}$ (for every $P\in\mathcal S_{b,n}$ the share of each single party has the same law for every message), and:
--
--   1. each share has $b+1$ bits ($|\{0,1\}\times V|=2^{b+1}$), and $|\mathcal K_n|=(2n-1)2^b$;
--   2. every $P\in\mathcal S_{b,n}$ is uniform on a set $Z$ of keys with $(n-1)2^b\le|Z|\le n2^b$, and $H_\infty(P)\ge b+\log_2(n-1)$;
--   3. for every $\ell\ge1$ and every function $\mathrm{Ext}:\mathcal K_n\to\{0,1\}^\ell$,
--   $$\max_{P\in\mathcal S_{b,n}}\mathrm{TV}\big(\mathrm{Ext}(K),U_\ell\big)\ge\frac1{4n-2},\qquad K\sim P;$$
--   4. for $\ell=1$ some function of the index alone attains equality in item 3: there is $g:V\to\{0,1\}$ such that $\mathrm{Ext}(k)=g(\text{index of }k)$ has error at most $1/(4n-2)$ on every $P\in\mathcal S_{b,n}$ and exactly $1/(4n-2)$ on some $P\in\mathcal S_{b,n}$.
--
--   For $n=2$ this is the bound $1/6$ of Theorem 1.1, and item 4 shows that $1/6$ is exact. The theorem extends the main result to $n$ parties: the source class suffices for perfect two-out-of-$n$ sharing, yet no extractor gets a bit closer than $1/(4n-2)$ to uniform.
--
--   **Formalization Note** Correctness and privacy are the published Definition 2.1 predicates `PerfectlyCorrect 2` and `IsPrivate 2 0` (TV $=0$ for every coalition of fewer than two parties). TV is the $\tfrac12\ell^1$ distance, logarithms are base 2, and $\{0,1\}^\ell$ is `Fin ℓ → Bool`. The hypothesis $2^b>n\ge2$ implies $b\ge2$.
--
--   Differences from the source:
--   - generalization: fix distinct nonzero α_1, …, α_n → the theorem holds for every injective α : Fin n → 𝔽_{2^b} with all α_j ≠ 0; reason: the paper's choice is arbitrary; such α exist since 2^b − 1 ≥ n, so the statement specializes to the paper's
--   - encoding: each share has b + 1 bits → Fintype.card (Share b) = 2^(b+1); reason: the share alphabet is {0,1} × 𝔽_{2^b}
--   - encoding: max_{P∈𝒮_{b,n}} TV(Ext(K), U_ℓ) ≥ 1/(4n − 2) → ∃ P ∈ 𝒮_{b,n} with TV(Ext(K), U_ℓ) ≥ 1/(4n − 2); reason: 𝒮_{b,n} is finite and nonempty, so the maximum is attained
--   - encoding: some function of the index i alone attains equality in item 3 → ∃ g : V → {0,1}^1 with error ≤ 1/(4n − 2) on every P ∈ 𝒮_{b,n} and = 1/(4n − 2) on some P; reason: "attains equality in the max-bound" unfolded
--   - encoding: parties [n], central keys c ∈ [n−1] → Fin n, Fin (n−1), counted from 0; reason: relabelling
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), Theorem 4.1, pp.8–9 (PDF pp.8–9); construction §4.1, displays (5), (6), p.8

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_SSNonExt_IsPrivate
import Definitions.Def_SSNonExt_Supplement_shrN

namespace SSNonExt.Supplement

open SSNonExt

/-- **Theorem 4.1.** "Let n ≥ 2 and let b satisfy 2^b > n. The scheme Π_{b,n} is a perfectly correct
two-out-of-n scheme for b-bit messages that is perfectly private for 𝒮_{b,n}, and: 1. each share has
b + 1 bits, and the key set 𝒦_n has (2n − 1)2^b elements; 2. every distribution in 𝒮_{b,n} is uniform on
a set of between (n − 1)2^b and n2^b keys, and hence has min-entropy at least b + log(n − 1); 3. for
every ℓ ≥ 1 and every function Ext : 𝒦_n → {0, 1}^ℓ, max_{P∈𝒮_{b,n}} TV(Ext(K), U_ℓ) ≥ 1/(4n − 2),
K ∼ P; 4. for ℓ = 1, some function of the index i alone attains equality in item 3."
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), Theorem 4.1, pp.8–9 (PDF pp.8–9); construction §4.1, displays (5), (6),
p.8.

**Formalization Note.**
* Stated for **every** choice of distinct nonzero `α_1, …, α_n ∈ 𝔽_{2^b}` (`α` injective and nonzero),
  the paper's "fix distinct nonzero elements".
* Correctness and privacy are Definition 2.1 with `t = 2` (every set of ≥ 2 parties reconstructs; the
  law of each set of < 2 parties' shares does not depend on the message, `δ = 0`).
* Item 1: "b + 1 bits" is the size `2^{b+1}` of the share alphabet `{0,1} × 𝔽_{2^b}`.
* Item 3: "max over 𝒮_{b,n} ≥ c" is "some `P ∈ 𝒮_{b,n}` has error ≥ c"; `{0,1}^ℓ` is `Fin ℓ → Bool`.
* Item 4: "attains equality in item 3" is: the error of `g ∘ index` is at most `1/(4n − 2)` on every
  source of the class and equal to it on some source, with ℓ = 1.
* Logarithms are base 2. `b ≥ 2` follows from `2^b > n ≥ 2`. -/
theorem theorem_4_1 (b n : ℕ) (hn : 2 ≤ n) (hbn : n < 2 ^ b) (α : Fin n → V b)
    (hα_inj : Function.Injective α) (hα0 : ∀ j, α j ≠ 0) :
    PerfectlyCorrect 2 (shrN (b := b) α) ∧
      IsPrivate 2 0 (srcClassN (b := b) hn) (shrN α) ∧
      (Fintype.card (Share b) = 2 ^ (b + 1) ∧ Fintype.card (KeyN b n) = (2 * n - 1) * 2 ^ b) ∧
      (∀ P ∈ srcClassN (b := b) hn,
        (∃ (Z : Finset (KeyN b n)) (hZ : Z.Nonempty),
          P = PMF.uniformOfFinset Z hZ ∧ (n - 1) * 2 ^ b ≤ Z.card ∧ Z.card ≤ n * 2 ^ b) ∧
        (haveI := keyN_nonempty (b := b) hn;
          (b : ℝ) + Real.logb 2 ((n : ℝ) - 1) ≤ minEntropy P)) ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ Ext : KeyN b n → (Fin ℓ → Bool),
        ∃ P ∈ srcClassN (b := b) hn,
          1 / (4 * (n : ℝ) - 2) ≤ TV (P.map Ext) (PMF.uniformOfFintype (Fin ℓ → Bool))) ∧
      (∃ g : V b → (Fin 1 → Bool),
        (∀ P ∈ srcClassN (b := b) hn,
          TV (P.map (g ∘ keyIndexN)) (PMF.uniformOfFintype (Fin 1 → Bool)) ≤ 1 / (4 * (n : ℝ) - 2)) ∧
        (∃ P ∈ srcClassN (b := b) hn,
          TV (P.map (g ∘ keyIndexN)) (PMF.uniformOfFintype (Fin 1 → Bool)) = 1 / (4 * (n : ℝ) - 2))) := by sorry

end SSNonExt.Supplement
