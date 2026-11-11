-- Prove2me | Theorems.Thm_SpectralFeedback_lidskii_reverse_order
-- name    : SpectralFeedback.lidskii_reverse_order
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:34.131608+00:00
-- url     : https://prove2.me/theorems/15ed1810-2ab4-4b11-9468-5a72a5e1c5b5
-- title:
--   Lidskii's reverse-order inequality $\lambda^\downarrow(H)+\lambda^\uparrow(L)\prec\lambda(H+L)$ [Hia97, Thm 1.6]
-- statement:
--   Let $H,L\in\mathbb C^{n\times n}$ be Hermitian. Write $\lambda^\downarrow(H)$ for the eigenvalues of $H$ in decreasing order and $\lambda^\uparrow(L)$ for those of $L$ in increasing order. Then
--
--   $$
--   \lambda^\downarrow(H)+\lambda^\uparrow(L)\ \prec\ \lambda(H+L),
--   $$
--
--   where $x\prec y$ ($x$ is majorized by $y$) means that, after sorting both vectors decreasingly, every partial sum of the first $k$ entries of $x$ is at most that of $y$, with equal totals.
--
--   In the paper this is applied to $H=K$ and $L=JKJ$ (a block Gram matrix and its conjugate by $J=\mathrm{diag}(I_s,-I_s)$), which have the same spectrum $\lambda$, so the left side is the duplicated paired spectrum $c\oplus c$.
--
--   **Formalization Note** $\lambda^\downarrow_i(H)$ is `eigDesc H i` (0-based) and $\lambda^\uparrow_i(L)=\lambda^\downarrow_{n-1-i}(L)$. Majorization is the published `RetailVariety.Fashion.Majorized`, which sorts both vectors itself.
--
--   Differences from the source:
--   - encoding: $\lambda^\downarrow(H)+\lambda^\uparrow(L)\prec\lambda(H+L)$ → `Majorized (fun i => eigDesc H i + eigDesc L (n-1-i)) (fun i => eigDesc (H+L) i)`; reason: Lean indexing convention; $\lambda^\uparrow_i = \lambda^\downarrow_{n-1-i}$ (0-based); the order of $\lambda(H+L)$ is irrelevant to majorization
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), proof of Lemma F.3, p.93 (PDF p.95), citing [Hia97] F. Hiai, Log-majorizations and norm inequalities for exponential operators, Banach Center Publ. 38 (1997), Theorem 1.6; also proof of Theorem H.2, p.109 (PDF p.111)

import Mathlib
import Definitions.Def_SpectralFeedback_eigDesc
import Definitions.Def_RetailVariety_Fashion_Majorization

namespace SpectralFeedback

/-- **Lidskii's reverse-order inequality** [Hia97, Theorem 1.6], as stated in the proof of Lemma F.3
(Qi, *Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination*,
manuscript (Nov. 2026), p.93 (PDF p.95); also used in the proof of Theorem H.2, p.109): "Lidskii's
classical reverse-order inequality states that `λ↓(H) + λ↑(L) ≺ λ(H + L)` for Hermitian `H, L`."

**Formalization Note** `λ↓_i(H)` is `eigDesc H i` (0-based, decreasing); the increasing
rearrangement `λ↑_i(L)` is `λ↓_{n−1−i}(L)`. `x ≺ y` ("`x` is majorized by `y`") is the published
`RetailVariety.Fashion.Majorized x y`, which sorts both vectors itself, so the order of `λ(H + L)`
is immaterial. -/
theorem lidskii_reverse_order (n : ℕ) (H L : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hL : L.IsHermitian) :
    RetailVariety.Fashion.Majorized
      (fun i : Fin n => eigDesc H (i : ℕ) + eigDesc L (n - 1 - (i : ℕ)))
      (fun i : Fin n => eigDesc (H + L) (i : ℕ)) := by sorry

end SpectralFeedback
