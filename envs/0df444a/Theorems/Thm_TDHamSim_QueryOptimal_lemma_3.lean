-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_lemma_3
-- name    : TDHamSim.QueryOptimal.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:18:14.703333+00:00
-- url     : https://prove2.me/theorems/eb215a50-23fa-4672-a3b9-4b461de11252
-- title:
--   Lemma 3 — local Cayley identity
-- statement:
--   Let $K$ be Hermitian with norm at most $\alpha>0$, let $0<w\le1$, and let $O$ be a Hermitian unitary whose zero-ancilla compression is $K/\alpha$. For the local operator $R$ and catalyst $x$ of (17) and (21), $R$ is unitary and, for every input vector $\psi$,
--
--   $$R(\psi\oplus Ox)=U^C\psi\oplus x.$$
--
--   Here $x$ is computed from the midpoint of that input. This is an equality of vectors without a normalization condition on the input or the catalyst.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Lemma 3 — local Cayley identity, p.14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Cayley

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Lemma 3, p.14: unitarity and the local identity on every input vector. -/
theorem lemma_3 {n a : ℕ} (K : Mat (Bits n)) (O : Mat (Bits a × Bits n))
    (α w : ℝ) (hα : 0 < α) (hw : 0 < w) (hw1 : w ≤ 1)
    (hK : K.IsHermitian) (hbound : opNorm K ≤ α)
    (hO : O.IsHermitian) (hOU : IsUnitary O)
    (hblock : ∀ x y, O ((fun _ => false), x) ((fun _ => false), y) = (α : ℂ)⁻¹*K x y) :
    IsUnitary (localR a n w) ∧ ∀ v : Ket (Bits n),
      act (localR a n w) (join v (act O (act (catalyst α w K O) v))) =
        join (act (cayley α w K) v) (act (catalyst α w K O) v) := by sorry

end TDHamSim.QueryOptimal
