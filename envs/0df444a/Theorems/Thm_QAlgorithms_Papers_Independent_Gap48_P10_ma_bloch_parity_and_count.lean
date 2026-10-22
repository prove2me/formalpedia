-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_bloch_parity_and_count
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.ma_bloch_parity_and_count
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:23:15.054986+00:00
-- url     : https://prove2.me/theorems/d54843f3-28d2-4d20-8170-ce5c7c35d81d
-- title:
--   Lemma 4.10: Bloch parity and exact T-count
-- statement:
--   Let $M$ be a Matsumoto–Amano expression and $k$ the least natural exponent for which $(\sqrt2)^k\widehat M$ has every entry in $\mathbb Z[\sqrt2]$. Write $p_k$ for reduction of the constant quadratic-integer coefficient modulo two after scaling, and $\sim$ for permutation of columns. Put
--
--   $$
--   P_T=\begin{pmatrix}1&1&0\\1&1&0\\0&0&0\end{pmatrix},\quad
--   P_H=\begin{pmatrix}0&0&0\\1&1&0\\1&1&0\end{pmatrix},\quad
--   P_S=\begin{pmatrix}1&1&0\\0&0&0\\1&1&0\end{pmatrix}.
--   $$
--   Exactly one of the following holds: $k=0$ and $M$ denotes a Clifford operator; $k>0$, $p_k(\widehat M)\sim P_T$ and the first syllable is $T$; $k>0$, $p_k(\widehat M)\sim P_H$ and it is $HT$; or $k>0$, $p_k(\widehat M)\sim P_S$ and it is $SHT$. Moreover,
--
--   $$
--   \operatorname{Tcount}(M)=k.
--   $$
--   The chronological elementary expansion has exactly this many actual $T$ letters. The exponent is that of the Bloch matrix, not the original $2\times2$ matrix.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 4, Lemma 4.10: Bloch parity and exact T-count

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Lemma 4.10, PDF pp.4-5, including its last clause on p.5.
Exactly one of all four parity/left-syllable cases holds, and the BLOCH least
common denominator exponent is exactly the actual normal-form T-count. -/
theorem ma_bloch_parity_and_count (M : NormalForm) :
    (∃! tag : Fin 4, blochCase M tag) ∧
    normalTCount M = realLde (operatorBloch (maValue M)) ∧
    letterTCount (normalWord cliffordH cliffordSH M) = realLde (operatorBloch (maValue M)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
