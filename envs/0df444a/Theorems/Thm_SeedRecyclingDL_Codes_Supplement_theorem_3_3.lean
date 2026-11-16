-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_Supplement_theorem_3_3
-- name    : SeedRecyclingDL.Codes.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:41:48.484558+00:00
-- url     : https://prove2.me/theorems/8ce3d380-db7c-4ee6-8f5f-87f2d57ccffa
-- title:
--   Theorem 3.3 — Efficient codes for splittable channels
-- statement:
--   Let $E=(E_n)_{n\ge1}$ be a channel on binary words: each input $u\in\{0,1\}^n$ has a set $E_n(u)\subseteq\{0,1\}^*$ of possible outputs with $u\in E_n(u)$. Two inputs are confusable if they share an output, and a code $C\subseteq\{0,1\}^n$ corrects $E_n$ if no two distinct codewords are confusable. Let $c\ge0$ and $C\ge1$ be constants and let $L=L(n)\ge1$ be an integer computable from $n$ in $\mathrm{poly}(n)$ time with $\log_2 L=O(\log_2 n)$. Assume that for all sufficiently large $n$ and every split $n=m+N$ with $1\le N\le n/2$:
--
--   1. there is a reflexive symmetric relation $R_N$ on $\{0,1\}^N$ whose maximum degree satisfies $D_N\le C N^c$, such that $E_n$ is $(m,N,R_N)$-splittable (whenever $x\Vert s$ and $x'\Vert s'$ with $|x|=|x'|=m$, $|s|=|s'|=N$ are confusable, $(s,s')\in R_N$), and every $R_N$-neighbourhood can be listed in $\mathrm{poly}(N)$ time;
--   2. for each $x\in\{0,1\}^m$ a set $\widetilde\Gamma(x)$ with $\Gamma_E(x)\subseteq\widetilde\Gamma(x)\subseteq\{0,1\}^m\setminus\{x\}$ and $|\widetilde\Gamma(x)|\le L$ can be listed in $\mathrm{poly}(n)$ time, where $\Gamma_E(x)$ is the set of payloads $x'\ne x$ with $x\Vert s$ confusable with $x'\Vert s$ for some $s\in\{0,1\}^N$;
--   3. for every string $y$, the preimage set $E_n^{-1}(y)=\{z\in\{0,1\}^n: y\in E_n(z)\}$ can be listed in $\mathrm{poly}(n+|y|)$ time,
--
--   all listing algorithms being uniform and deterministic. Then there are a uniform deterministic encoder and decoder such that, for all sufficiently large $n$, the encoder maps messages of some length $M(n)$ injectively to words of length $n$, its image $C_n$ corrects $E_n$, and
--
--   $$
--   n-\log_2|C_n|\;\le\;\log_2 L(n)+c\,\log_2\log_2 n+O(1).
--   $$
--
--   Encoding takes $\mathrm{poly}(n)$ bit operations on every message, and the decoder runs in $\mathrm{poly}(n+|y|)$ bit operations on every word $y$ and returns the transmitted message whenever $y\in E_n(\mathrm{Enc}(\mu))$.
--
--   This is the general form of the paper's construction: any channel that splits at a fixed boundary and has efficiently listable competitors and preimages admits explicit codes whose redundancy exceeds $\log_2 L$ only by $c\log_2\log_2 n+O(1)$. The Damerau–Levenshtein codes of Theorem 4.3 are built on the same pattern.
--
--   **Formalization Note** The hypotheses are the published predicate `GeneralChannelAssumptions G` of the base mission; the exponent $c$ is `G.degreeExponent` and $L$ is `G.L`. Programs run on the published charged RAM; the encoder program is run from the initial machine state, so any precomputation (field, lookup tables) is charged to every encoding. All constants, the two programs and the threshold $n_0$ are chosen after the channel data and before $n$. Logarithms are base 2.
--
--   Differences from the source:
--   - encoding: binary strings in {0,1}^n and {0,1}^* → lists of Fin 2 with length predicates; reason: the published Word representation of the base mission; fixed lengths are predicates, so received words of every length remain in scope
--   - encoding: hypotheses (a)–(c) on E, c ≥ 0, C ≥ 1 and the poly(n)-time computable integer L(n) ≥ 1 with log L = O(log n), for all sufficiently large n and every split n = m + N with 1 ≤ N ≤ n/2 → the published predicate GeneralChannelAssumptions G (c = G.degreeExponent, C = G.degreeConstant, L = G.L); reason: the base mission defines this predicate as exactly these hypotheses, with the constants, programs and threshold quantified before n; nothing is added or dropped
--   - encoding: asymptotic deterministic bit complexity → finite programs with actual charged RAM executions and uniform positive constants before lengths and inputs; reason: the fixed instruction semantics generates costs; a function with an assigned runtime is not accepted
--   - reading: bit operations on a RAM without a prescribed tape layout → helper routines use length and packed-value natural cells, while main and generic decoders receive raw bit streams; reason: each cell read and output is charged by bit length; raw decoder streams permit bounded inspection of arbitrarily long invalid inputs
--   - reading: an explicit code with deterministic poly(n)-time encoding → one encoder program, fixed before n, whose execution from the initial machine state on every message of length M(n) outputs its codeword within K(n+1)^d bit operations; the code is the image of this encoder; reason: the source proof builds the field and the lookup tables of A in poly(n) time, so charging that construction to every encoding call keeps the bound poly(n); the code is the object the program computes
--   - reading: poly(n + |y|)-time decoding → one decoder program, fixed before n, that halts within K(n+|y|+1)^d on every finite word y and returns the encoded message on every y ∈ E_n(Enc(µ)); reason: "decoding" is the recovery of the transmitted message of §3.2; the runtime is stated for every string y, as in hypothesis (c)
--   - reading: a reflexive symmetric relation R_N for each split, whose R_N-neighbourhoods are listed in poly(N) time → one relation G.relation N and one neighbour list G.neighbors N per suffix length N, shared by every n ≥ n₀ with N ≤ n/2, listed by a program run at parameter N; reason: the source indexes the relation, its degree D_N and the listing time by N alone, and a uniform poly(N)-time listing algorithm on s ∈ {0,1}^N cannot depend on n
--   - encoding: the O(1) in (13) and "for all sufficiently large n" → a real constant K₀ and a threshold n₀, both chosen after G and before n; reason: O(1) depends only on the fixed channel family and its constants, never on n
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Theorem 3.3, printed p. 10 (PDF p. 12); Definition 3.1 and (5)–(9), printed pp. 8–9 (PDF pp. 10–11); proof printed p. 10 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Interfaces

set_option autoImplicit false

namespace SeedRecyclingDL.Codes.Supplement

/-- Bui–Hagiwara–Wang–Vu, STOC 2027 submission #1449, Theorem 3.3, printed
p. 10 (PDF p. 12). The hypotheses (a)–(c), c ≥ 0, C ≥ 1 and the poly(n)-time
computable L(n) ≥ 1 with log L = O(log n) are exactly the published
`GeneralChannelAssumptions`; c is `G.degreeExponent` and L is `G.L`.
"Explicit code with deterministic poly(n)-time encoding and poly(n + |y|)-time
decoding": one encoder program and one decoder program, fixed before n, whose
actual charged executions compute the code's encoder on every message (in
K(n+1)^d bit operations, any table construction included) and its decoder on
every finite word y (in K(n+|y|+1)^d). The code is the image of that encoder.
The O(1) of (13) is a constant K₀ fixed before n. -/
theorem theorem_3_3 (G : GeneralChannelData) (hG : GeneralChannelAssumptions G) :
    ∃ (encoder decoder : Program) (M : ℕ → ℕ) (Enc : ℕ → Word → Word)
      (Dec : ℕ → Word → Option Word) (K₀ K : ℝ) (d n₀ : ℕ), 0 < K ∧
      ∀ n : ℕ, n₀ ≤ n →
        let code : Set Word := {c | ∃ mu : Word, mu.length = M n ∧ c = Enc n mu}
        (∀ mu : Word, mu.length = M n → (Enc n mu).length = n) ∧
        (∀ mu nu : Word, mu.length = M n → nu.length = M n →
          Enc n mu = Enc n nu → mu = nu) ∧
        Corrects G.channel n code ∧
        redundancy n code ≤
          log₂ (G.L n) + G.degreeExponent * log₂ (log₂ n) + K₀ ∧
        (∀ mu y : Word, mu.length = M n → y ∈ G.channel n (Enc n mu) →
          Dec n y = some mu) ∧
        (∀ mu : Word, mu.length = M n →
          Executes encoder n (mu.map Fin.val) (some ((Enc n mu).map Fin.val))
            (K * (n + 1 : ℝ) ^ d)) ∧
        (∀ y : Word,
          Executes decoder n (y.map Fin.val) ((Dec n y).map (List.map Fin.val))
            (K * (n + y.length + 1 : ℕ) ^ d)) := by sorry

end SeedRecyclingDL.Codes.Supplement
