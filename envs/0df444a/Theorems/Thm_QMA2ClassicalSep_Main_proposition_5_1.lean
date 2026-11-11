-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_proposition_5_1
-- name    : QMA2ClassicalSep.Main.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:52.832112+00:00
-- url     : https://prove2.me/theorems/65006590-3137-4548-b1f0-caf404e077c7
-- title:
--   Proposition 5.1 — YES instances have zero separable energy
-- statement:
--   Let $k\ge2$, $N=2^k$, $|\mathcal X_A|=|\mathcal X_B|=N^3$. For every parameter $((\pi_p)_{p\in[N]},h_A,h_B)$ of the hard YES distribution $\mathcal D_+$ — independent permutations $\pi_p$ of $V$, signs $h_A,h_B$, edge signs $\sigma_p(x)=\chi(x)\chi(\pi_p(x))$ with $\chi(x)=h_A(x_A)h_B(x_B)$ — the Hamiltonian $H$ of Equation (1) satisfies
--
--   $$
--   \lambda_{\mathrm{sep}}(H)=0 .
--   $$
--
--   Every instance in the support of $\mathcal D_+$ is therefore a YES instance of Problem 4.1, with a zero-energy product witness.
--
--   Differences from the source:
--   - encoding: every instance in the support of 𝒟₊ → every YES parameter; reason: 𝒟₊ is a product of uniform distributions, so every parameter is in its support
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 19, Proposition 5.1

import Definitions.Def_QMA2ClassicalSep_Main_HardDist

namespace QMA2ClassicalSep.Main

theorem proposition_5_1 (k : ℕ) (hk : 2 ≤ k) (ω : YESParam k) :
    lamSep (yesInst ω).Ham = 0 := by sorry

end QMA2ClassicalSep.Main
