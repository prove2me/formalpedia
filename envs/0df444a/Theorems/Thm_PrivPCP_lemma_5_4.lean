-- Prove2me | Theorems.Thm_PrivPCP_lemma_5_4
-- name    : PrivPCP.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:42:35.903533+00:00
-- url     : https://prove2.me/theorems/72231088-113c-4ea8-bdea-6fa5bf682f6b
-- title:
--   Lemma 5.4: parameter selection
-- statement:
--   For every $c>0$ there is a constant $C\ge1$ (absolute once $c$ is) with the following property. Let $n\ge1$ and $k\ge2$. Then there are a prime $q$, subgroups $S_i\le\mathbb F_q^\times$ of orders $s_i$, subgroups $\Gamma_i\le S_i$ of orders $h_i$ and elements $\zeta_i\in\mathbb F_q^\times$, with grids $D=\prod_iH_i$, $H_i=\zeta_i\Gamma_i$, $\Omega=\prod_iS_i$ and $N=\prod_is_i$, such that, writing $d_i=h_i+\lceil s_i/128\rceil$, $v_i=7d_i+2h_i-2$, $\eta=1/128$ and $\lambda_k=k\log(k+1)$:
--
--   1. **Degree margins.** $d_i-h_i\ge\eta s_i$ and $v_i+1\le s_i/4$ for every $i$.
--   2. **Domain sizes.**
--   $$n<|D|<N\le C^k\max\{n\log(n+1)\lambda_k^k,\ \lambda_k^{2k}\},\qquad\tfrac14\le s_i/s_j\le4,$$
--   and $2^{\sum_i\lfloor\log_2h_i\rfloor}\ge c\,n\log(n+1)$.
--   3. **Field and subgroups.** The $h_i$ are distinct primes, the $s_i$ are pairwise coprime, $N\mid q-1$, $N<q\le N^6$, $H_i\cap S_i=\emptyset$, and $H_i$ and $S_i$ are invariant under multiplication by $\Gamma_i$.
--
--   These parameters make the grids satisfy Lemma 8.1 and Conjecture 4.2's coprimality and balance at $\eta=1/128$, $\beta=4$, and give $q\le N^6$ through Xylouris's form of Linnik's theorem.
--
--   **Formalization Note** $\log$ is the natural logarithm, $\lfloor\log_2h\rfloor$ is the integer binary logarithm, and $|D|=\prod_ih_i$ because $|\zeta_i\Gamma_i|=h_i$.
--
--   Differences from the source:
--   - generalization: $c$ the absolute constant of Lemma 8.1 → every $c>0$, with $C$ depending on $c$; reason: at Lemma 8.1's $c$ this is the paper's statement; the proof works for any $c$ by enlarging $A$
--   - encoding: $k=k(n)\ge2$ any integer function of $n$ → every $n\ge1$ and every $k\ge2$, $C$ independent of both; reason: the same quantification
--   - encoding: grids $D=\prod_iH_i$, $H_i=\zeta_i\Gamma_i\subseteq\mathbb F_q$ → $H_i=\{\zeta_i\gamma:\gamma\in\Gamma_i\}$ in $\mathbb F_q^\times$, $|D|=\prod_ih_i$; reason: same sets
--   - encoding: $d_i$, $v_i$ of §5.2 → $h_i+\lceil s_i/128\rceil$ and $7d_i+2h_i-2$ written out in the statement; reason: the paper's standing choice (p.28)
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Lemma 5.4, p.29 (PDF p.31); §5.2, choice of d_i, p.28 (PDF p.30)

import Mathlib

namespace PrivPCP

/-- **Lemma 5.4 (Parameter selection)** (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027
submission manuscript (sha256 c2cac1e0…), Lemma 5.4, p.29, with the choices of §5.2, p.28). There is an absolute
constant `C ⩾ 1` such that for every `n ⩾ 1` and every `k ⩾ 2` there are a prime `q`, subgroups
`S_i ⩽ 𝔽_q^×` of orders `s_i`, subgroups `Γ_i ⩽ S_i` of orders `h_i` and elements `ζ_i ∈ 𝔽_q^×`, with grids
`D = ∏_i H_i`, `H_i = ζ_i Γ_i`, `Ω = ∏_i S_i`, `N = ∏_i s_i`, such that, with `d_i = h_i + ⌈s_i/128⌉`,
`v_i = 7d_i + 2h_i − 2`, `η = 1/128`, `λ_k = k log(k+1)`:
1. `d_i − h_i ⩾ η s_i` and `v_i + 1 ⩽ s_i/4`;
2. `n < |D| < N ⩽ C^k max{n log(n+1) λ_k^k, λ_k^{2k}}`, `1/4 ⩽ s_i/s_j ⩽ 4`, and
   `2^{∑_i ⌊log₂ h_i⌋} ⩾ c n log(n+1)`;
3. the `h_i` are distinct primes, the `s_i` pairwise coprime, `N ∣ q − 1`, `N < q ⩽ N⁶`, `H_i ∩ S_i = ∅`, and
   `H_i`, `S_i` are invariant under multiplication by `Γ_i`.

**Formalization Note** The paper fixes `c` as "the absolute constant in Lemma 8.1"; here the statement is made
for every `c > 0`, with `C` depending on `c`. "Any integer function `k = k(n)`" is every pair `n ⩾ 1`, `k ⩾ 2`,
with `C` independent of both. The grids are written through the subgroups: `|D| = ∏_i h_i` since
`|ζ_i Γ_i| = h_i`, and `H_i = {ζ_i γ : γ ∈ Γ_i}`. `log` is the natural logarithm and `⌊log₂ h⌋` is `Nat.log 2 h`;
`v_i` is computed in `ℕ`, where `7d_i + 2h_i ⩾ 2`. -/
theorem lemma_5_4 : ∀ c : ℝ, 0 < c → ∃ C : ℝ, 1 ≤ C ∧
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 2 ≤ k →
    ∃ (q : ℕ) (h s : Fin k → ℕ) (S Γ : Fin k → Subgroup (ZMod q)ˣ) (ζ : Fin k → (ZMod q)ˣ),
      q.Prime ∧
      (∀ i, Nat.card (S i) = s i ∧ Nat.card (Γ i) = h i ∧ Γ i ≤ S i) ∧
      -- 1. degree margins
      (∀ i, (1 / 128 : ℝ) * s i ≤ ((h i + ⌈(s i : ℝ) / 128⌉₊ : ℕ) : ℝ) - h i ∧
        ((7 * (h i + ⌈(s i : ℝ) / 128⌉₊) + 2 * h i - 2 + 1 : ℕ) : ℝ) ≤ (s i : ℝ) / 4) ∧
      -- 2. domain sizes
      n < ∏ i, h i ∧ ∏ i, h i < ∏ i, s i ∧
      ((∏ i, s i : ℕ) : ℝ) ≤ C ^ k * max ((n : ℝ) * Real.log (n + 1) * ((k : ℝ) * Real.log (k + 1)) ^ k)
        (((k : ℝ) * Real.log (k + 1)) ^ (2 * k)) ∧
      (∀ i j, (1 / 4 : ℝ) ≤ (s i : ℝ) / s j ∧ (s i : ℝ) / s j ≤ 4) ∧
      c * n * Real.log (n + 1) ≤ (2 : ℝ) ^ (∑ i, Nat.log 2 (h i)) ∧
      -- 3. field and subgroup choices
      (∀ i, (h i).Prime) ∧ Function.Injective h ∧ (∀ i j, i ≠ j → Nat.Coprime (s i) (s j)) ∧
      (∏ i, s i) ∣ q - 1 ∧ ∏ i, s i < q ∧ q ≤ (∏ i, s i) ^ 6 ∧
      (∀ i, ∀ γ ∈ Γ i, ζ i * γ ∉ S i) ∧
      (∀ i, ∀ γ ∈ Γ i, ∀ x : (ZMod q)ˣ,
        ((∃ γ' ∈ Γ i, x = ζ i * γ') → ∃ γ' ∈ Γ i, γ * x = ζ i * γ') ∧ (x ∈ S i → γ * x ∈ S i)) := by sorry

end PrivPCP
