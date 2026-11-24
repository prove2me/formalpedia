-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_lemma_I_3
-- name    : SRAudit.TwoPhase.Supplement.lemma_I_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:29:13.754809+00:00
-- url     : https://prove2.me/theorems/fc09994b-2667-461c-ad6d-2dbd2ce55754
-- title:
--   Lemma I.3, OA-60 — Λ(m,n,k) is positive definite when m + n + k > 0
-- statement:
--   For $m,n,k\in\mathbb N_0$ with $m+n+k>0$, the symmetric block matrix
--   $$\Lambda(m,n,k)=\begin{bmatrix}2D_m & R_{2k,m}^{\mathsf T} & J_{m,n}\\ R_{2k,m} & \widetilde D_{2k} & Q_{2k,n}\\ J_{n,m} & Q_{2k,n}^{\mathsf T} & 2D_n\end{bmatrix}$$
--   of (I.3)–(I.4) is positive definite.
--
--   The Jacobian of the tier-2 pseudogradient is $-2\beta\Lambda(t_a,t_b,t_{ab})$, so this lemma gives diagonal strict concavity and hence uniqueness of the tier-2 equilibrium in Proposition C.3(b).
--
--   Differences from the source:
--   - encoding: 2k × n matrices Q_{2k,n}, R_{2k,m} and D̃_{2k} with rows 1, …, 2k → rows indexed by Fin k × Fin 2 in lexicographic order; reason: the same matrices; (l,0) is the odd row 2l+1, (l,1) the even row 2l+2
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-60, Lemma I.3 (matrices (I.3)–(I.4), OA-55)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Supplement_LambdaMatrix

namespace SRAudit.TwoPhase.Supplement

theorem lemma_I_3 (m n k : ℕ) (h : 0 < m + n + k) : (Lambda m n k).PosDef := by sorry

end SRAudit.TwoPhase.Supplement
