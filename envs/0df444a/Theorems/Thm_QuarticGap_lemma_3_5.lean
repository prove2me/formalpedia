-- Prove2me | Theorems.Thm_QuarticGap_lemma_3_5
-- name    : QuarticGap.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:43.120391+00:00
-- url     : https://prove2.me/theorems/feb5faa1-5ff2-45a4-bd69-c0c9233add6e
-- title:
--   Lemma 3.5 — verifying (13): the distance of $x_S$ from $\bar x$ and the deviation of $\|x\|^2$ from $d$
-- statement:
--   Let $F$ be the sine or the cosine test, with $F_\infty = 1$ and $F_\infty = 2$ respectively. Let $f$ be a Boolean function, $x \in \mathbb C^Y$ nonzero, $\gamma \in \mathbb C^S$, $\beta \in \mathbb C$, $d > 0$. Let $x_S$ be the restriction of $x$ to $S$, and let $\bar x \in \mathbb C^S$ have coordinates $\bar x_s = (\gamma_s+\beta Z_s(f))/\sqrt K$. Then
--   $$
--   \Bigl|\sum_{j\in Y} p_x(j)F(f,j)-\Phi(f)\Bigr| \le F_\infty\Bigl(\frac{\|x_S-\bar x\|(\|x_S\|+\|\bar x\|)}{\|x\|^2}+\frac{\|\bar x\|^2\,\bigl|\|x\|^2-d\bigr|}{d\,\|x\|^2}\Bigr).
--   $$
--
--   All applications verify the hypothesis of the transfer theorem by this bound.
--
--   Differences from the source:
--   - encoding: a set of K characters → a nonempty Finset S with K = S.card; reason: the source divides by K and takes log(2K); K = 0 is meaningless
--   - encoding: Y ⊇ S → an embedding e of S into Y; reason: the source itself identifies S with coordinates of the outcome set
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 3.5, p.26

import Mathlib
import Definitions.Def_QuarticGap_Phi

open QAlgorithms

namespace QuarticGap

/-- Lemma 3.5 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.26). For the sine or cosine test, a Boolean
function `f`, a nonzero `x ∈ ℂ^Y`, `γ ∈ ℂ^S`, `β ∈ ℂ`, `d > 0`, with `x_S` the restriction of `x` to
`S` and `x̄_s = (γ_s + βZ_s(f))/√K`:
`|∑_{j∈Y} p_x(j)F(f, j) − Φ(f)| ≤ F∞ (∥x_S − x̄∥(∥x_S∥ + ∥x̄∥)/∥x∥² + ∥x̄∥² |∥x∥² − d|/(d ∥x∥²))`. -/
theorem lemma_3_5 {m : ℕ} (hm : 2 ≤ m) (S : Finset (Qubits m)) (hS : S.Nonempty) {Y : Type*} [Fintype Y] (e : S ↪ Y)
    (k : TestKind) (f : Qubits m → ℤˣ) (x : Y → ℂ) (hx : x ≠ 0) (γ : S → ℂ) (β : ℂ) (d : ℝ)
    (hd : 0 < d) :
    let xS : S → ℂ := fun s => x (e s)
    let xbar : S → ℂ := fun s => (γ s + β * (Zs f s : ℂ)) / (Real.sqrt S.card : ℂ)
    |∑ j, lenSqDist x j * testF k e f j - Phi k S γ β d f| ≤
      Finf k * (l2 (xS - xbar) * (l2 xS + l2 xbar) / l2 x ^ 2 +
        l2 xbar ^ 2 * |l2 x ^ 2 - d| / (d * l2 x ^ 2)) := by sorry

end QuarticGap
