-- Prove2me | Theorems.Thm_SymCircMM_lemma_2_12_entry_invariant
-- name    : SymCircMM.lemma_2_12_entry_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:30:35.848936+00:00
-- url     : https://prove2.me/theorems/700846e2-7e52-40ea-8408-f7561af87f52
-- title:
--   Lemma 2.12 — each entry $(AB)_{i\ell}$ is $S_n$-invariant under the action (2)
-- statement:
--   Let $\sigma\in S_n$ act on the variables by $\sigma\cdot A_{ij}=A_{i,\sigma(j)}$ and $\sigma\cdot B_{j\ell}=B_{\sigma(j),\ell}$ (display (2)), and on polynomials by renaming. Then for all $i,\ell\in[n]$
--
--   $$\sigma\cdot (AB)_{i\ell}=\sigma\cdot\sum_{j}A_{ij}B_{j\ell}=(AB)_{i\ell}.$$
--
--   In particular each entry is invariant under every subgroup of $S_n$, such as $G_k$. This is why a symmetric circuit for $\mathrm{MM}_n$ can fix each output gate.
--
--   Differences from the source:
--
--   - encoding: the index set [n] = {1, …, n} → a finite type ι with n = card ι; reason: a relabelling of the index set
--   - encoding: the action (σ · f)(x_1, …, x_N) = f(σ · x_1, …, σ · x_N) on polynomials → MvPolynomial.rename (mmAct σ); reason: renaming the variables is this action
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Lemma 2.12, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_SymCircMM_MMVar

set_option autoImplicit false

namespace SymCircMM

/-- **Lemma 2.12** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.6 (PDF p.7)): "Each entry (AB)_{iℓ} is individually S_n-invariant
(hence G_k-invariant) under the action (2)." For every permutation `σ` of the inner index, renaming the
variables by (2) fixes each entry polynomial `∑_j A_{aj} B_{jb}`.

**Formalization Note.** `[n]` is any finite type `ι`; invariance under every `σ ∈ S_n` gives
invariance under every subgroup, in particular `G_k`. -/
theorem lemma_2_12_entry_invariant {ι : Type} [Fintype ι] (F : Type) [Field F]
    (σ : Equiv.Perm ι) (a b : ι) :
    MvPolynomial.rename (mmAct σ) (mmEntry F a b) = mmEntry F a b := by sorry

end SymCircMM
