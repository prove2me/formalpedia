-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_Supplement_explicit_list_recoverable_codes
-- name    : SubspaceEvasion312.Explicit.Supplement.explicit_list_recoverable_codes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:50:21.790753+00:00
-- url     : https://prove2.me/theorems/ec7404fc-1d63-492a-9a31-b79f70361edf
-- title:
--   Theorem 33 — explicit codes, list-recoverable with list size O((ℓ/ε²) log(ℓ/ε))
-- statement:
--   There are absolute constants $K_1,K_2,h$ with the following property. For every integer $\ell\ge1$ and every $\varepsilon\in(0,1)$ there is $K$ such that for every $R\in(0,1)$ there are a finite field $\mathbb F_q$, an alphabet $\Sigma=\mathbb F_q^s$ with
--   $$|\Sigma|=q^s\le\exp\!\big(\exp(K_1\ell^2/\varepsilon^2)\big),$$
--   an ordering of $\mathbb F_q$, one encoding program $P$ and a threshold $n_0$ such that for every $n\ge n_0$ there is a code $C_n\subseteq\Sigma^n$ (not necessarily additive) with
--
--   1. $\mathrm{rate}(C_n)=\log_{|\Sigma|}|C_n|/n\ge R$;
--   2. $C_n$ is $\big(1-R-\varepsilon,\ \ell,\ \lfloor K_2(\ell/\varepsilon^2)(1+\log_2(\ell/\varepsilon))\rfloor\big)$ list-recoverable;
--   3. $P$, given $n$ and the base-$q$ digits of an index $i<|C_n|$, outputs the $i$-th codeword under a bijection onto $C_n$, within charged time and word bound $K(n+1)^h$.
--
--   For list decoding ($\ell=1$) and list recovery, this gives explicit codes with list size $O((\ell/\varepsilon^2)\log(\ell/\varepsilon))$ at radius $1-R-\varepsilon$, a doubly exponential alphabet and encoding time $O_{\ell,\varepsilon}(1)\cdot\mathrm{poly}(n)$.
--
--   **Formalization Note** $K$ depends on $\ell,\varepsilon$ only. When $R+\varepsilon>1$ the radius is negative and the recovered lists are empty. Time is measured in the mission's published register machine (field operations one step, program size charged).
--
--   Differences from the source:
--   - reading: there are explicit codes → for every n ≥ n₀ a code C_n ⊆ (F_q^s)^n over a finite field chosen in the proof, encoded by one program uniform in n; reason: explicit code families are indexed by all large block lengths; the alphabet F_q^s is the one the proof produces
--   - reading: alphabet size exp(exp(O(ℓ²/ε²))) → q^s ≤ exp(exp(K₁ℓ²/ε²)) with absolute K₁ chosen first; reason: uniform reading of O
--   - reading: list size O((ℓ/ε²) log(ℓ/ε)) → ⌊K₂(ℓ/ε²)(1 + log₂(ℓ/ε))⌋ with absolute K₂ chosen first; reason: a raw log bound with an absolute constant fails at ℓ = 1, ε → 1 with R + ε ≤ 1, where a nonempty code has a list of size at least 1; for ℓ/ε ≥ 2 the two forms differ by a factor at most 2
--   - reading: encoding time O_{ℓ,ε}(1) poly(n) → charged time and word bound K(n+1)^h with absolute h and K depending on ℓ, ε only; reason: the displayed O_{ℓ,ε} allows no dependence on R
--   - encoding: rate of a code over Σ → log_q |C_n| / (s n) = log_{|Σ|} |C_n| / n; reason: definition of rate
--   - encoding: encoding of a nonlinear code → bijection from indices 0, …, |C_n|−1, input as base-q digits, onto C_n; reason: printed p. 7 constructability convention
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, Explicit Subspace Evasive Sets via Subspace Designs, STOC 2027 submission #312 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf, PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc, Theorem 33, printed p. 15 (PDF p. 16); composition of Theorems 24, 32 and 28

import Definitions.Def_SubspaceEvasion312_Explicit_Supplement_codes

namespace SubspaceEvasion312.Explicit.Supplement
/-- Theorem 33, printed p.15 (PDF p.16). Absolute K1, K2, h precede l, eps, R; the
time factor K depends on l and eps only. The codes are subsets of (F_q^s)^n, alphabet
F_q^s, for every n >= n0, with one encoding program uniform in n. The list bound
K2 (l/eps^2)(1 + log2(l/eps)) is the uniform form of O((l/eps^2) log(l/eps)). -/
theorem explicit_list_recoverable_codes :
    ∃ K₁ K₂ h : ℕ, 0 < K₁ ∧ 0 < K₂ ∧
    ∀ (ℓ : ℕ) (ε : ℝ), 1 ≤ ℓ → 0 < ε → ε < 1 →
    ∃ K : ℕ, 0 < K ∧
    ∀ R : ℝ, 0 < R → R < 1 →
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (s n₀ : ℕ)
      (alphabet : Fin (Fintype.card F) ≃ F) (enc : Program F),
      0 < s ∧
      (((Fintype.card F) ^ s : ℕ) : ℝ) ≤ Real.exp (Real.exp ((K₁ : ℝ) * (ℓ : ℝ) ^ 2 / ε ^ 2)) ∧
      ∀ n ≥ n₀, ∃ Cn : Set (Blocks F s n),
        R ≤ setRate Cn ∧
        SetListRecoverable Cn (1 - R - ε) ℓ
          ⌊(K₂ : ℝ) * ((ℓ : ℝ) / ε ^ 2) * (1 + log₂ ((ℓ : ℝ) / ε))⌋₊ ∧
        EncodableSet Cn alphabet enc [n] (K * (n + 1) ^ h) (K * (n + 1) ^ h) := by sorry
end SubspaceEvasion312.Explicit.Supplement
