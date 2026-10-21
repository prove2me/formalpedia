-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P01_multiplicity_output
-- name    : QAlgorithms.Papers.Independent.Claimed50.P01.multiplicity_output
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:30:37.694669+00:00
-- url     : https://prove2.me/theorems/d4d6a891-a292-4c9a-8d0f-05d69502cded
-- title:
--   The classical path decodes the multiplicity basis label with its exact Born weight
-- statement:
--   Let $d\ge2$, $n\ge1$, fix the coherent CG operations independently of the input, and let $\lambda\vdash_d n$. Let $\mathcal P(\lambda)$ be the valid Young-lattice paths ending at $\lambda$, and let $P_\lambda$ denote the symmetric-group irreducible module. There is a bijection, chosen before the density operator $\rho$,
--
--   $$
--   e_\lambda:\mathcal P(\lambda)\longrightarrow\{0,\ldots,\dim P_\lambda-1\}.
--   $$
--
--   For every density operator $\rho$ on $(\mathbb C^d)^{\otimes n}$ and every multiplicity basis index $i$, the modified Algorithm 1 reports $(\lambda,i)$ by reading its classical path. With $p=e_\lambda^{-1}(i)$ and $B_p=\Pi_{\lambda,p}^{\mathrm{Sch}}U_n^{\mathrm{Sch}}$, its joint output probability is
--
--   $$
--   \Pr[(\Lambda,I)=(\lambda,i)]
--   =\operatorname{Tr}(\rho B_p^\dagger B_p).
--   $$
--
--   The multiplicity label is a basis index, not an arbitrary vector in $P_\lambda$. Decoding it uses the classical history and does not require storing the multiplicity register coherently. At $n=1$ there is one path and one multiplicity label.
-- source:
--   Weak Schur sampling with logarithmic quantum memory, arXiv:2309.11947v1, PDF p. 9, III, post-Theorem-1 observation

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P01

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Claimed50.P01

attribute [local instance] Classical.propDecidable

/-- The classical path determines exactly one symmetric-group basis label;
its joint Young/multiplicity probability is the corresponding Born weight
(PDF pp.8-9, footnotes 3,7 and the post-Theorem-1 observation). The decoding
bijection is chosen independently of rho, and p is a basis index, not a vector. -/
theorem multiplicity_output {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (C : CGSystem d) (lambda : Schur.Partition d n) :
    ∃ decode : PathsTo lambda ≃ Fin (Module.finrank ℂ (Schur.spechtSpace lambda)),
      ∀ (rho : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ), IsDensityMatrix rho →
      ∀ i : Fin (Module.finrank ℂ (Schur.spechtSpace lambda)),
        multiplicityProbability C decode i rho =
          effectProb ((schurBlock C (decode.symm i).val)ᴴ *
            schurBlock C (decode.symm i).val) rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P01

end
