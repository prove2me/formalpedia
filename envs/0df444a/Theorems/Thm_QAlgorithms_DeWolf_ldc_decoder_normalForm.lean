-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_ldc_decoder_normalForm
-- name    : QAlgorithms.DeWolf.ldc_decoder_normalForm
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:42:55.599161+00:00
-- url     : https://prove2.me/theorems/e506b0dd-e91e-4922-a98f-3a215fa63171
-- title:
--   Katz–Trevisan normal form for decoders of locally decodable codes
-- statement:
--   This is a normal form for the decoders of locally decodable codes.
--
--   Recall that $C : \{0,1\}^n \to \{0,1\}^N$ is a $(q,\delta,\varepsilon)$-locally decodable code (LDC) if for every $i \in [n]$ there is a classical randomized decoding algorithm making at most $q$ (possibly adaptive) queries to an $N$-bit string $y$ such that for all $x \in \{0,1\}^n$ and all $y$ with Hamming distance $d(C(x), y) \le \delta N$ it outputs $x_i$ with probability at least $\frac12 + \varepsilon$.
--
--   There are absolute constants $c_1, c_2 > 0$ with the following property. Let $C$ be a $(q,\delta,\varepsilon)$-LDC with $\delta > 0$ and $\varepsilon > 0$, and let $i \in [n]$. Then there is a family $M_i$ of pairwise disjoint subsets ("tuples") $t \subseteq [N]$, each with $|t| \le q$, such that
--
--   $$
--   |M_i| \ge c_1 \frac{\delta \varepsilon N}{q^2},
--   $$
--
--   and a bit $a_{i,t}$ for each $t \in M_i$, such that for every $t \in M_i$
--
--   $$
--   \Pr_{x \in \{0,1\}^n}\Bigl[x_i = a_{i,t} \oplus \bigoplus_{j \in t} C(x)_j\Bigr] \ge \frac12 + c_2 \frac{\varepsilon}{2^q},
--   $$
--
--   where $x$ is uniformly distributed.
--
--   Thus a decoder may simply query a uniformly random tuple of $M_i$ and output the parity of the answers plus $a_{i,t}$. This is the first step of the quantum lower bound for 2-query LDCs.
--
--   **Formalization Note** The randomized decoder is a probability distribution over decision trees of depth at most $q$ (adaptive queries allowed). For $q = 0$ the size bound is read with Lean's convention $1/0 = 0$; no $0$-query LDC with $\varepsilon>0$ and $n \ge 1$ exists anyway.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 143, §15.3, Fact 1. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Information
set_option autoImplicit false

namespace QAlgorithms.DeWolf


/-- de Wolf p.143, Fact 1 (Katz & Trevisan + folklore). There are absolute constants `c₁, c₂ > 0`
such that for every `(q, δ, ε)`-LDC `C : {0,1}^n → {0,1}^N` (with `δ, ε > 0`) and every `i ∈ [n]`
there is a set `M_i` of pairwise disjoint tuples of at most `q` indices of `[N]`, with
`|M_i| ≥ c₁ δ ε N / q²`, and a bit `a_{i,t}` for each `t ∈ M_i`, such that for each `t ∈ M_i`,
`Pr_x[x_i = a_{i,t} ⊕ ⊕_{j ∈ t} C(x)_j] ≥ 1/2 + c₂ ε / 2^q` for uniform `x ∈ {0,1}^n`. -/
theorem ldc_decoder_normalForm :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (n N q : ℕ) (δ ε : ℝ) (C : (Fin n → Bool) → (Fin N → Bool)),
        0 < δ → 0 < ε → IsLDC q δ ε C →
        ∀ i : Fin n, ∃ M : Finset (Finset (Fin N)),
          (M : Set (Finset (Fin N))).PairwiseDisjoint id ∧
          (∀ t ∈ M, t.card ≤ q) ∧
          c₁ * (δ * ε * (N : ℝ) / (q : ℝ) ^ 2) ≤ (M.card : ℝ) ∧
          ∃ a : Finset (Fin N) → Bool, ∀ t ∈ M,
            1 / 2 + c₂ * (ε / (2 : ℝ) ^ q) ≤
              ((Finset.univ.filter fun x : Fin n → Bool =>
                  x i = xor (a t) (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) /
                (2 : ℝ) ^ n := by
  sorry


end QAlgorithms.DeWolf
