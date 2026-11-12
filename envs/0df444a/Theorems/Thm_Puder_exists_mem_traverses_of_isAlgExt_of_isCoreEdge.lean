-- Prove2me | Theorems.Thm_Puder_exists_mem_traverses_of_isAlgExt_of_isCoreEdge
-- name    : Puder.exists_mem_traverses_of_isAlgExt_of_isCoreEdge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:05:07.891446+00:00
-- url     : https://prove2.me/theorems/a560a240-9f2d-4538-9920-3e85de8adb46
-- title:
--   Puder–Parzanchevski, Claim 4.2 — if H ≤_alg J then η_{H→J} is onto: every edge of Γ_X(J) is crossed by an element of H
-- statement:
--   Let $H, J \le \mathbf F_d$ with $J$ an algebraic extension of $H$ (`Puder.IsAlgExt H J`). Then every edge of the core graph $\Gamma_X(J)$ (`Puder.IsCoreEdge J g x`: the $x$-labelled edge leaving the coset $Jg$, crossed by the reduced walk of some element of $J$) is crossed by the reduced walk of some element $h \in H$ (`Puder.Traverses J h i g x` for some position $i$).
--
--   Puder, p. 14, proof of Lemma 4.1: “First, we claim that every edge is traced at least once (in fact, even more generally, if $H \le_{alg} N$ then $\eta^X_{H\to N}$ is onto: see Definition 5.3 and e.g. [PP15, Claim 4.2]. We repeat the simple argument here.)”
--
--   *Formalization note.* "$\eta^X_{H\to N}$ is onto" is stated on edges, which is the form the proof uses: every edge of $\Gamma_X(N)$ lies in the image of $\Gamma_X(H)$, that is, is crossed by the walk of some element of $H$. No finite generation is assumed.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 14), proof of Lemma 4.1, which cites D. Puder and O. Parzanchevski, *Measure preserving words are primitive*, J. Amer. Math. Soc. 28 (2015) 63–97, https://doi.org/10.1090/S0894-0347-2014-00796-7, Claim 4.2.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 14, proof of Lemma 4.1 (η_{H→N} is onto when H ≤_alg N), which cites Puder, D. and Parzanchevski, O., Measure preserving words are primitive, J. Amer. Math. Soc. 28 (2015) 63–97, https://doi.org/10.1090/S0894-0347-2014-00796-7, Claim 4.2

import Mathlib
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore

namespace Puder

theorem exists_mem_traverses_of_isAlgExt_of_isCoreEdge {d : ℕ} (H J : Subgroup (FreeGroup (Fin d)))
    (halg : IsAlgExt H J) (g : FreeGroup (Fin d)) (x : Fin d) (hcore : IsCoreEdge J g x) :
    ∃ h ∈ H, ∃ i : ℕ, Traverses J h i g x := by
  sorry

end Puder
