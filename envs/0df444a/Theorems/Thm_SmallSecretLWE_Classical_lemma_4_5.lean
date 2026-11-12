-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_lemma_4_5
-- name    : SmallSecretLWE.Classical.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:28:02.331537+00:00
-- url     : https://prove2.me/theorems/5dfb8870-c7d2-43ec-996e-65bff05cd8d4
-- title:
--   Lemma 4.5 — an $R$-faraway set has at most $\binom nl(q-1)^l/\binom{\lfloor R/2\rfloor+l}{l}$ points
-- statement:
--   Let $R\ge0$ and let $S\subseteq(\mathbb Z_q^n)_l$ be $R$-faraway. Then
--   $$|S|\le\frac{\binom{n}{l}(q-1)^l}{\binom{\lfloor R/2\rfloor+l}{l}} .$$
--   As printed the lemma carries no upper bound on $R$.
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: '$R$-faraway: $\|u-v\|_1>R$ for all $u,v\in S$' → for all distinct $u,v\in S$; reason: the literal reading allows only $S=\emptyset$
--   - reading: $R$ (range not stated) → hypothesis $0\le R$, $\lfloor R/2\rfloor$ as `Nat.floor`; reason: $R$ is the relaxation parameter $R\ge0$ of Definition 2.2, standing throughout §4
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 20, Lemma 4.5

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Kikuchi

namespace SmallSecretLWE.Classical

/-- Lemma 4.5. Let `R ≥ 0` and `S ⊆ (Z_q^n)_l` be `R`-faraway. Then
`|S| ≤ binom(n, l)(q − 1)^l / binom(⌊R/2⌋ + l, l)`. -/
theorem lemma_4_5 {n q l : ℕ} [NeZero q] (R : ℝ) (hR : 0 ≤ R) (S : Finset (KVert n q l))
    (hS : IsFaraway R S) :
    (S.card : ℝ) ≤ (n.choose l : ℝ) * ((q : ℝ) - 1) ^ l / ((⌊R / 2⌋₊ + l).choose l : ℝ) := by sorry

end SmallSecretLWE.Classical
