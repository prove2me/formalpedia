-- Prove2me | Theorems.Thm_VWZClique_scaled_matrix_multiplication_word_ram
-- name    : VWZClique.scaled_matrix_multiplication_word_ram
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T13:23:19.934841+00:00
-- url     : https://prove2.me/theorems/1d8354b5-188a-437a-b74d-529c82b36049
-- title:
--   Scaled integer matrix multiplication in near-$\omega$ time on the word RAM
-- statement:
--   For every $\eta>0$ and every fixed input-size exponent $d$, one finite word-RAM program takes two row-major $n\times n$ integer matrices $A,B$ with entry magnitudes at most $n^d$. For every $n\ge2$ it halts within $C n^{\omega_{\mathbb C}+\eta}$ instructions, using words of $w(\lfloor\log_2 n\rfloor+1)$ bits. Each signed output word is exactly the corresponding entry of $\sigma^{1+\lfloor\log_b n\rfloor}AB$, where $b\ge2$ and $\sigma>0$ are constants of the chosen algorithm. The scale is common to the whole matrix. The two inputs and the output occupy three consecutive row-major arrays, with their addresses and the dimension supplied in four designated cells.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good, Appendix A, pp. 21–22, especially p. 22, paragraph “To implement a matrix product”. This theorem isolates the scaled integer multiplication subroutine. https://zamir.prof/kclq.pdf

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_TrulySubcubicAPSP_WordRAM

theorem VWZClique.scaled_matrix_multiplication_word_ram (η : ℝ) (hη : 0<η) (d : ℕ) :
    ∃ (b w : ℕ) (σ : ℤ) (P : List TrulySubcubicAPSP.Instr) (C : ℝ),
      2≤b ∧ 0<w ∧ 0<σ ∧ 0<C ∧
      ∀ (n : ℕ), 2≤n → ∀ (A B : Matrix (Fin n) (Fin n) ℤ) (m : ℤ → ℤ),
        (∀ i j, |A i j|≤(n:ℤ)^d) → (∀ i j, |B i j|≤(n:ℤ)^d) →
        m (-30)=0 → m (-31)=((n*n:ℕ):ℤ) → m (-32)=((2*(n*n):ℕ):ℤ) → m (-34)=(n:ℤ) →
        (∀ i j : Fin n, m ((n*i.val+j.val:ℕ):ℤ)=A i j) →
        (∀ i j : Fin n, m ((n*n+(n*i.val+j.val):ℕ):ℤ)=B i j) →
        ∃ t : ℕ, (t:ℝ)≤C*(n:ℝ)^(OAI.MatrixMultiplication.Arithmetic.omega ℂ+η) ∧
          ∃ out : ℤ → BitVec (w*(n.log2+1)),
            TrulySubcubicAPSP.exec P t 0 (fun z => BitVec.ofInt _ (m z))=some (true,out) ∧
            ∀ i j : Fin n, (out ((2*(n*n)+(n*i.val+j.val):ℕ):ℤ)).toInt=
              σ^(Nat.log b n+1)*(A*B) i j := by sorry
