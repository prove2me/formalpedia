-- Prove2me | Theorems.Thm_RedundancyStab_IID_copy_arrival_rate
-- name    : RedundancyStab.IID.copy_arrival_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:04.396819+00:00
-- url     : https://prove2.me/theorems/45e57f16-7ac0-461e-8ccf-c7068439abc2
-- title:
--   Proof of Lemma 2, p. 26 — |C(s)| = C(K−1, d−1) and the arrival rate of copies to a server is λC(K−1,d−1)/C(K,d) = λd/K
-- statement:
--   Let $1\le d\le K$, let $C$ be the set of $d$-element subsets of the servers $S=\{1,\dots,K\}$ and $C(s)=\{c\in C: s\in c\}$. Types arrive at rate $\lambda/\binom{K}{d}$ each, so copies arrive at server $s$ at rate $|C(s)|\,\lambda/\binom{K}{d}$. Then $|C(s)|=\binom{K-1}{d-1}$ and
--   $$\frac{\lambda\binom{K-1}{d-1}}{\binom{K}{d}}=\frac{\lambda d}{K}.$$
--
--   This is the arrival term of the drift (14) of the number of copies at a server.
--
--   **Formalization Note** The real number $\lambda$ is arbitrary (the identity is linear in it); `typesAt K d s` is $C(s)$.
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, p. 26, proof of Lemma 2 (and |C(s)| on p. 5)

import Mathlib
import Definitions.Def_RedundancyStab_IID_Model

namespace RedundancyStab.IID

theorem copy_arrival_rate (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam : ℝ) (s : Fin K) :
    (typesAt K d s).card = (K - 1).choose (d - 1) ∧
      ((typesAt K d s).card : ℝ) * lam / (K.choose d : ℝ) = lam * d / K := by sorry

end RedundancyStab.IID
