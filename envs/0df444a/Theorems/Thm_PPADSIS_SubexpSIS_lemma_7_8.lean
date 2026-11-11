-- Prove2me | Theorems.Thm_PPADSIS_SubexpSIS_lemma_7_8
-- name    : PPADSIS.SubexpSIS.lemma_7_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:50:10.411514+00:00
-- url     : https://prove2.me/theorems/e427be68-a81e-4d6c-9bed-8272c14b3d8e
-- title:
--   Lemma 7.8 — the SIS puzzle is efficient and tree-structured, and hard at difficulty 2^λ under Assumption 7.7
-- statement:
--   Let $e,\nu$ be the constants of Assumption 7.7, $0<e<5/9$ and $4e/5<\nu<1-e$, and let $(F_{\mathrm{sis}},D_{\mathrm{sis}})$ be the SIS puzzle of §7.3 for $e$. Then $(F_{\mathrm{sis}},D_{\mathrm{sis}})$ satisfies the efficiency and tree structure properties of Definition 4.3. Under Assumption 7.7, every polynomial-size adversary $A$ outputs $F_{\mathrm{sis}}(2^\lambda,\hat{\mathbf A})$, for $\hat{\mathbf A}\leftarrow D_{\mathrm{sis}}(2^\lambda,1^\lambda)$, with negligible probability:
--   $$\Pr\bigl[A_\lambda(\hat{\mathbf A})=F_{\mathrm{sis}}(2^\lambda,\hat{\mathbf A}) : \hat{\mathbf A}\leftarrow D_{\mathrm{sis}}(2^\lambda,1^\lambda)\bigr]\le\delta(\lambda)$$
--   for a negligible $\delta$ depending on $A$, the probability over the sampler's and the adversary's coins.
--
--   Together with a uuSNARG that is state-unique against adversaries of size about $2^\lambda$, this hard computation at the single difficulty $2^\lambda$ is what Theorem 4.7 turns into a hard distribution of RSVL, and then of EOML, in the proof of Corollary 7.9.
--
--   Differences from the source:
--   - generalization: "(F_sis, D_sis) satisfies the efficiency and tree structure properties" → also the length bounds of the puzzle syntax of §4.2 ($|F(t,x)|\le\mathrm{poly}(\log t,|x|)$, $|x|\le\mathrm{poly}(\log t,\lambda)$); reason: §4.2 presupposes them of every puzzle; dropping the clause gives the source's statement.
--   - reading: "Let e and ν be constants" (Assumption 7.7) → real $e,\nu$ with $0<e<5/9$, $4e/5<\nu<1-e$, as hypotheses of the whole lemma; reason: the lemma is stated in the context of Assumption 7.7's constants; the first clause does not involve $\nu$.
--   - encoding: "$F(t,x)$ runs in time $t\cdot\mathrm{poly}(\log t,|x|)$" → one machine within $(t+1)(\log t+|x|+2)^k$ steps on `encNat t ++ x`; reason: equal up to a factor 2 for $t\ge1$, and $\log 0$ is undefined.
--   - encoding: $D_{\mathrm{sis}}$ "samples a uniform matrix and outputs it" → a concrete coin algorithm with $(|\mathrm{input}|+2)^3$ coins whose output law is exactly uniform, outputting the matrix code with its dimensions and modulus; reason: the paper fixes no implementation or encoding.
--   - encoding: $F_{\mathrm{sis}}$ on a string that encodes no matrix → $(0,0^p)$; reason: the paper defines $F_{\mathrm{sis}}$ on matrices only.
--   - encoding: "outputs $F_{\mathrm{sis}}(2^\lambda,\hat{\mathbf A})$" → the adversary's output string equals $F_{\mathrm{sis}}(2^\lambda,\hat{\mathbf A})$; non-uniform adversaries with one circuit per input length; reason: Lean representation of the adversary model of p. 20.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 58, Lemma 7.8

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_SISPuzzle
import Definitions.Def_PPADSIS_SubexpSIS_Assumption

namespace PPADSIS.SubexpSIS

theorem lemma_7_8 (e ν : ℝ) (he₀ : 0 < e) (he₁ : e < 5 / 9) (hν₀ : 4 * e / 5 < ν)
    (hν₁ : ν < 1 - e) :
    (sisPuzzle e).SyntaxBounds ∧ (sisPuzzle e).Efficient ∧ (sisPuzzle e).TreeStructured ∧
    (Assumption77 e ν → ∀ A : Adversary, A.PolySize → ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ lam : ℕ,
      coinAvg ((sisPuzzle e).D.numCoins (2 ^ lam, lam)) (fun c =>
        A.prob lam ((sisPuzzle e).D.run (2 ^ lam, lam) (List.ofFn c))
          (fun y => y = (sisPuzzle e).F (2 ^ lam)
            ((sisPuzzle e).D.run (2 ^ lam, lam) (List.ofFn c)))) ≤ δ lam) := by sorry

end PPADSIS.SubexpSIS
